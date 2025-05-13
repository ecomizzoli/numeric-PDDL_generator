package translations;

import log.LogFile;
import model.DeclareModel;
import org.deckfour.xes.in.XesXmlParser;
import org.deckfour.xes.model.XLog;
import org.processmining.ltl2automaton.plugins.automaton.Automaton;
import org.processmining.ltl2automaton.plugins.automaton.DOTExporter;

import Automaton.VariableSubstitutionDefinition;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class IOManager {
  
  private static IOManager ioManager;
  private String projectPrefix = "";
  private String resourcesFolder;
  private String inputFolder;
  private String libFolder;
  private String outputFolder;
  private String pddlFolder;
  //private String alignmentFolder = outputFolder + "alignments" + File.separator;
  
  private IOManager() {
    this.setPaths();
  }

  public static IOManager getInstance() {
    if (ioManager == null) {
      ioManager = new IOManager();
    }
    return ioManager;
  }

  private void setPaths() {
    this.resourcesFolder = this.projectPrefix + "src" + File.separator + "main" + File.separator + "resources" + File.separator;
    this.inputFolder = resourcesFolder + "input" + File.separator;
    this.libFolder = resourcesFolder + "lib" + File.separator;
    this.outputFolder = resourcesFolder + "output" + File.separator;
    this.pddlFolder = outputFolder + "pddl" + File.separator;

    // Create folders if these don't exist.
    File inputDir = new File(inputFolder);
    if (!inputDir.exists()) {
      inputDir.mkdirs();
    }
    File outputDir = new File(outputFolder);
    if (!outputDir.exists()) {
      outputDir.mkdirs();
    }
    File pddlDir = new File(pddlFolder);
    if (!pddlDir.exists()) {
      pddlDir.mkdirs();
    }
  }

  public void setProjectPrefix(String projectPrefix) {
    this.projectPrefix = projectPrefix + File.separator;
    this.setPaths();
  }
  
  //Section: Reading declare model
  public DeclareModel readDeclareModel(String modelFileName) {
    File declareFile = new File(inputFolder + modelFileName);
    HashMap<String, ArrayList<String[]>> parsedLines = readFile(declareFile);
    return new DeclareModel(parsedLines);
  }
  
  private HashMap<String, ArrayList<String[]>> readFile(File declareFile) {
    HashMap<String, ArrayList<String[]>> lines = initializeSortingMap();
    Pattern[] declarePatterns = getCompiledPatterns();
    try (Scanner scanner = new Scanner(declareFile)) {
      while (scanner.hasNextLine()) {
        String line = scanner.nextLine();
        addToMap(line, lines, declarePatterns);
      }
    } catch (IOException e) {
      System.err.println(declareFile.getAbsolutePath());
      System.out.println("Error reading the declare file");
    }
    return lines;
  }

  public String readDomain() {
    StringBuilder sb = new StringBuilder();

    File domain = new File(this.libFolder + "domain.pddl");
    Scanner s;
    try {
      s = new Scanner(domain);
      while (s.hasNextLine()) {
        sb.append(s.nextLine() + "\n");
      }
    } catch (FileNotFoundException e) {
      System.err.println("Domain file with placeholders not found!");
      e.printStackTrace();
    }
    return sb.toString();
  }

  public Map<String, Integer> readVariableAssignments(String fileName) {
    HashMap<String, Integer> map = new HashMap<>();
    File variablesFile = new File(this.inputFolder + fileName);

    try (Scanner scanner = new Scanner(variablesFile)) {
      while (scanner.hasNextLine()) {

        String line = scanner.nextLine();
        if (line.isEmpty()) continue;

        String[] read = line.split(" ");
        if (read.length != 2) {
          throw new Error("Parsing error!");
        }

        map.put(read[0], Integer.valueOf(read[1]));
      }
    } catch (IOException e) {
      System.err.println(e);
    }

    return map;
  }
  public Set<VariableSubstitutionDefinition> readVariablesSubstitutions(String fileName) {
    HashSet<VariableSubstitutionDefinition> set = new HashSet<>();

    File assignmentFile = new File(this.inputFolder + fileName);
    try (Scanner scanner = new Scanner(assignmentFile)) {
      while (scanner.hasNextLine()) {

        String line = scanner.nextLine();
        if (line.isEmpty()) continue;

        String[] read = line.split(" ");
        if (read.length <= 2) {
          throw new Error("Parsing error!");
        }

        VariableSubstitutionDefinition va = new VariableSubstitutionDefinition();
        va.activityName = read[0];
        va.categoryName = read[1];
        
        int i = 2;
        va.substitutionValues = new ArrayList<>();
        while (i < read.length) {
          va.substitutionValues.add(Integer.valueOf(read[i]));
          i++;
        }

        set.add(va);
      }
    } catch (IOException e) {
      System.err.println(e);
    }
    
    return set;
  }
  
  private HashMap<String, ArrayList<String[]>> initializeSortingMap() {
    HashMap<String, ArrayList<String[]>> lines = new HashMap<>();
    String[] lineDefinitions = {"activityLines", "bindingLines", "intAttributeLines", "floatAttributeLines", "enumAttributeLines", "unaryConstraintLines", "binaryConstraintLines"};
    for (String container : lineDefinitions) {
      lines.put(container, new ArrayList<>());
    }
    return lines;
  }
  
  private Pattern[] getCompiledPatterns() {
    Pattern activityPattern = Pattern.compile("^\\s*activity\\s+([a-z]+[a-z\\d]*)\\s*$");
    Pattern bindingPattern = Pattern.compile("^\\s*bind\\s+([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*:\\s+([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*$");
    
    Pattern intPattern = Pattern.compile("^\\s*([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*:\\s+integer\\s+between\\s+(-?\\d+)\\s+and\\s+(-?\\d+)\\s*$");
    Pattern floatPattern = Pattern.compile("^\\s*([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*:\\s+float\\s+between\\s+(-?\\d+\\.?\\d*)\\s+and\\s+(-?\\d+\\.?\\d*)\\s*$");
    Pattern enumPattern = Pattern.compile("^\\s*([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*:\\s+([a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*)\\s*$");
    
    Pattern unaryPattern = Pattern.compile("^([A-Za-z\\d]+)\\[([a-z]+[a-z\\d]*)]\\s+\\|\\s*([Aa-z\\d!=(),.<> -]*)\\|\\s*$");
    Pattern binaryPattern = Pattern.compile("^([A-Za-z\\d -]+)\\[([a-z]+[a-z\\d]*),\\s*([a-z]+[a-z\\d]*)]\\s+\\|\\s*([Aa-z\\d!=(),.<> -]*)\\|\\s*([Ta-z\\d!=(),.<> -]*)\\|\\s*$");
    
    Pattern numericConditionPattern = Pattern.compile("^\\s*[atAT].[a-z]+[a-z\\d]*\\s+(>=|<=|>|<|=|!=)\\s+-?\\d+.?\\d*\\s*$");
    Pattern enumConditionPattern = Pattern.compile("^\\s*[atAT].[a-z]+[a-z\\d]*\\s+(is not|is)\\s+[a-z]+[a-z\\d]*\\s*$*");
    Pattern listConditionPattern = Pattern.compile("^\\s*[atAT].[a-z]+[a-z\\d]*\\s+(not in|in)\\s+[a-z]+[a-z\\d]*(,\\s+[a-z]+[a-z\\d]*)*\\s*$");
    return new Pattern[] {
      activityPattern, 
      bindingPattern, 
      intPattern, 
      floatPattern, 
      enumPattern, 
      unaryPattern, 
      binaryPattern,
      numericConditionPattern, 
      enumConditionPattern, 
      listConditionPattern
    };
  }
    
    
  //Section: Lines validation and addition
  private void addToMap(String line, HashMap<String, ArrayList<String[]>> lines, Pattern[] patterns) {
    Matcher activityMatcher = patterns[0].matcher(line);
    Matcher bindingMatcher = patterns[1].matcher(line);
    Matcher intMatcher = patterns[2].matcher(line);
    Matcher floatMatcher = patterns[3].matcher(line);
    Matcher enumMatcher = patterns[4].matcher(line);
    Matcher unaryMatcher = patterns[5].matcher(line);
    Matcher binaryMatcher = patterns[6].matcher(line);
    
    if (activityMatcher.find()) {
      lines.get("activityLines").add(new String[] {activityMatcher.group(1)});
    } else if (bindingMatcher.find()) {
      lines.get("bindingLines").add(tokenizeBinding(bindingMatcher));
    } else if (enumMatcher.find()) {
      lines.get("enumAttributeLines").add(tokenizeEnumAttribute(enumMatcher));
    } else if (floatMatcher.find()) {
      lines.get("floatAttributeLines").add(tokenizeNumericAttribute(floatMatcher));
    } else if (intMatcher.find()) {
      lines.get("intAttributeLines").add(tokenizeNumericAttribute(intMatcher));
    } else if (binaryMatcher.find()) {
      if (isConditionValid(binaryMatcher.group(4), patterns) && isConditionValid(binaryMatcher.group(5), patterns)) {
        lines.get("binaryConstraintLines").add(tokenizeBinaryConstraint(binaryMatcher));
      } else {
        System.out.println("Error parsing condition: " + binaryMatcher.group(4) + " or " + binaryMatcher.group(5));
      }
    } else if (unaryMatcher.find()) {
      if (isConditionValid(unaryMatcher.group(3), patterns)) {
        lines.get("unaryConstraintLines").add(tokenizeUnaryConstraint(unaryMatcher));
      } else {
        System.out.println("Error parsing condition: " + unaryMatcher.group(3));
      }
    } else {
      System.out.println("Error parsing line: " + line);
    }
  }
  
  
  //Section: Tokenization of valid lines
  private String[] tokenizeBinding(Matcher matcher) {
    return new String[] {matcher.group(1), matcher.group(3)};
  }
  
  private String[] tokenizeEnumAttribute(Matcher matcher) {
    return new String[] {matcher.group(1), matcher.group(3)};
  }
  
  private String[] tokenizeNumericAttribute(Matcher matcher) {
    return new String[] {matcher.group(1), matcher.group(3), matcher.group(4)};
  }
  
  private String[] tokenizeUnaryConstraint(Matcher matcher) {
    return new String[] {matcher.group(1), matcher.group(2), matcher.group(3)};
  }
  
  private String[] tokenizeBinaryConstraint(Matcher matcher) {
    return new String[] {matcher.group(1), matcher.group(2), matcher.group(3), matcher.group(4), matcher.group(5)};
  }
  
  
  //Section: Condition syntax validation
  private boolean isConditionValid(String condition, Pattern[] patterns) {
    if (condition != null && !condition.isBlank()) {
      String conditionToCheck = condition.replaceAll("[)(]", "");
      String[] singleConditions = conditionToCheck.split(" and | or | AND | OR ");
      for (String subCondition : singleConditions) {
        if (!isSubConditionValid(subCondition, patterns)) {
          return false;
        }
      }
      return true;
    }
    return true;
  }
  
  private boolean isSubConditionValid(String condition, Pattern[] patterns) {
    Matcher numericMatcher = patterns[7].matcher(condition);
    Matcher enumMatcher = patterns[8].matcher(condition);
    Matcher listMatcher = patterns[9].matcher(condition);
    return numericMatcher.find() || enumMatcher.find() || listMatcher.find();
  }
  
  
  
  
  
  
  
  
  
  
  
  
  
  //Section: Exporting model
  public void exportModel(DeclareModel model) {
    try (FileWriter fileWriter = new FileWriter(outputFolder + "model.txt")) {
      fileWriter.write(model.toString());
    } catch (IOException e) {
      System.out.println("Error creating the model file");
    }
  }
  
  
  //Section: Reading log file
  public LogFile readLog(String logFileName, DeclareModel model) {
    File logFile = new File(inputFolder + logFileName);
    XLog xlog = null;
    XesXmlParser parser = new XesXmlParser();
    if (parser.canParse(logFile)) {
      try {
        xlog = parser.parse(logFile).get(0);
      } catch (Exception e) {
        System.out.println("Error reading the log file");
      }
    }
    return new LogFile(xlog, model);
  }
  
  
  //Section: Exporting log file
  public void exportLog(LogFile log) {
    try (FileWriter fileWriter = new FileWriter(outputFolder + "log.txt")) {
      fileWriter.write(log.toString());
    } catch (IOException e) {
      System.out.println("Error creating the model file");
    }
  }
  
  
  //Section: Exporting PDDL files
  public void exportProblemPDDL(String pddlContent, int traceNr) {
    try (FileWriter fileWriter = new FileWriter(pddlFolder + "problem" + traceNr + ".pddl")) {
      fileWriter.write(pddlContent);
    } catch (IOException e) {
      e.printStackTrace();
      System.out.println("Error creating the problem pddl");
    }
  }
  
  public void exportDomainPDDL(String pddlContent) {
    try (FileWriter fileWriter = new FileWriter(pddlFolder + "domain.pddl")) {
      fileWriter.write(pddlContent);
    } catch (IOException e) {
      System.out.println("Error creating the domain pddl");
    }
  }
  
  
  //Section: Reading cost model
  public List<String[]> readCostModel(String costsFileName) {
    File costModel = new File(inputFolder + costsFileName);
    List<String[]> costsList = new ArrayList<>();

    try (Scanner scanner = new Scanner(costModel)) {
      while (scanner.hasNextLine()) {
        costsList.add(scanner.nextLine().split(" "));
      }
    } catch (IOException e) {
      System.out.println("Error reading the cost model");
    }
    return costsList;
  }
  
  public void exportEquivalenceClasses(HashMap<String, ArrayList<String>> classes) {
    StringBuilder builder = new StringBuilder();
    for (Map.Entry<String, ArrayList<String>> eqClass : classes.entrySet()) {
      builder.append(eqClass.getKey()).append(" ");
      for (String classPart : eqClass.getValue()) {
        builder.append(classPart).append(" ");
      }
      builder.append("\n");
    }
    
    try (FileWriter fileWriter = new FileWriter(outputFolder + "equivalenceClasses.txt")) {
      fileWriter.write(builder.toString());
    } catch (IOException e) {
      System.out.println("Error creating the model file");
    }
  }
  
  public void exportToDot(Automaton automaton) throws IOException {
    DOTExporter.exportToDot(automaton, "MyAutomata", new FileWriter(outputFolder + File.separator + "automaton.dot"));
  }
}