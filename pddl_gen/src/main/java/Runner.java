import java.util.ArrayList;
import java.util.Map;
import java.util.Set;

import Automaton.VariableSubstitution;
import translations.IOManager;
import translations.PDDLGenerator;
import log.LogFile;
import model.DeclareModel;

public class Runner {

  public static void main(String[] args) throws Exception {

    if (args.length != 5) {
      String errString = new String(
        "Pass as args the names of the following files:\n" +
        "1: model\n" +
        "2: trace\n" +
        "3: variables\n" +
        "4: variable substitutions\n" +
        "5: cost model"
      );
      System.err.println(args.length);
      throw new Error(errString);
    }

    // args = new String[5];

    findAlignments(args[0], args[1], args[2], args[3], args[4]);
  }
  
  public static void findAlignments(
    String modelString, 
    String traceString, 
    String variablesString, 
    String substitutionsString, 
    String costsString) 
    throws Exception 
  {

    // Read model and logs to find ltl formula
    IOManager ioManager = IOManager.getInstance();

    // In case the jar you run is outside the directory in which the project is; Add directory name as prefix.
    ioManager.setProjectPrefix("pddl_gen");
    
    DeclareModel model = ioManager.readDeclareModel(modelString); // OKAY!
    model.assignCosts(ioManager.readCostModel(costsString)); // OKAY!

    Map<String, Integer> variableAssignments = ioManager.readVariableAssignments(variablesString);
    Set<VariableSubstitution> substitutions = ioManager.readVariablesSubstitutions(substitutionsString);

    System.out.println("Model: " + model);

    LogFile log = ioManager.readLog(traceString, model); // OKAY!
    
    ioManager.exportModel(model);

    // If formula exists, define and write PDDL problems.
    // PDDLGenerator pddlGenerator = new PDDLGenerator(model, ltlFormula);
    PDDLGenerator pddlGenerator = new PDDLGenerator(model);
    String domain = pddlGenerator.defineDomain();
    ArrayList<String> problems = log.generateProblems(pddlGenerator, variableAssignments, substitutions);
    int i = 1;
    for (String problem : problems) {
      IOManager.getInstance().exportProblemPDDL(problem, i);
      i++;
    }
    IOManager.getInstance().exportDomainPDDL(domain);
  }
}

