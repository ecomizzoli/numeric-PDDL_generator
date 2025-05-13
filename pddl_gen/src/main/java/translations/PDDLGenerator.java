package translations;

import model.Activity;
import model.Attribute;
import model.Condition;
import model.CostEnum;
import model.DeclareConstraint;
import model.DeclareModel;

import org.deckfour.xes.extension.std.XConceptExtension;
import Automaton.Automaton;
import Automaton.Pair;
import Automaton.State;
import Automaton.Transition;
import Automaton.VariableSubstitutionDefinition;
import log.Event;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class PDDLGenerator {

  private static final int CHANGE_DEFAULT_COST = 1;
  private static final int ADD_DEFAULT_COST = 2;
  private static final int SET_DEFAULT_COST = 1;
  private static final int DELETE_DEFAULT_COST = 2;

  private final Map<Pair<Activity, CostEnum>, Integer> costs;
  
  // NOTE Define action costs above ^^^
  private final HashMap<String, Activity> activities;
  private final ArrayList<DeclareConstraint> constraints;
  private ArrayList<Automaton> constraintAutomatons;
  private List<List<State>> goalAutomatonStates;
  private State finalTraceState;
  // private final ArrayList<Transition> relevantTransitions;

  private static final String HEADER_STRING = 
    "(define (problem prob-trace)\n" + 
    "  (:domain trace-alignment)\n" + 
    "\n";
  private static final String FOOTER_STRING = 
    "  (:metric minimize (total_cost))\n" +
    ")\n" +
    "\n";
  
  public PDDLGenerator(DeclareModel model) throws Exception {

    // Get set costs, or use default ones
    Map<Pair<Activity, CostEnum>, Integer> costs = model.getCosts();
    if (costs != null) {
      this.costs = costs;
    } else {
      this.costs = null;
    }

    this.activities = model.getActivities();
    this.constraints = model.getDeclareConstraints();
    this.constraintAutomatons = new ArrayList<>();
    this.goalAutomatonStates = new ArrayList<>();
    this.prepareAutomatonStates();
  }
  private void prepareAutomatonStates() {
    int index = 1;
    for (DeclareConstraint constraint : this.constraints) {
      String prefix = "s" + index++ + "_";
      Automaton newAutomaton = new Automaton(activities.keySet(), prefix, constraint);
      this.constraintAutomatons.add(newAutomaton);
      
      // Automaton might have more than one goal state. In that case, we'll put the goal states with an "or" between them.
      List<State> goalStates = newAutomaton.getStates().stream()
                                  .filter(x -> x.isGoal)
                                  .toList();

      this.goalAutomatonStates.add(goalStates);
    }
  }

  public String defineProblem(ArrayList<Event> listOfEvents, Set<VariableSubstitutionDefinition> substitutions) {

    Map<Event, Map<Attribute, String>> attributes = this.parseEvents(listOfEvents);
    List<State> finalAutomatonStates = new ArrayList<>();
    List<Condition> allReformedConditions = this.getAllReformedConditions();
    Map<Integer, String> mappingVariables = this.getMappingVariables(substitutions, attributes, allReformedConditions);

    StringBuilder s = new StringBuilder();
    s.append(PDDLGenerator.HEADER_STRING);
    s.append(this.buildObjectsString(attributes, mappingVariables));

    s.append(this.buildVariables(mappingVariables, substitutions));
    s.append(this.buildActionCosts(mappingVariables));
    s.append(this.buildTraceDeclaration(listOfEvents, attributes, mappingVariables));
    s.append(this.buildAutomatons(finalAutomatonStates, mappingVariables));

    s.append(this.buildGoals());
    s.append(PDDLGenerator.FOOTER_STRING);
    return s.toString();
  }

  private List<Condition> getAllReformedConditions() {

    List<Condition> list = new LinkedList<>();

    for (Automaton aut : this.constraintAutomatons) {
      for (Transition t : aut.getTransitions()) {
        List<Condition> reformConditions = t.getReformedConditions();
        if (reformConditions != null) {
          list.addAll(t.getReformedConditions());
        }
      }
    }
    return list;
  }

  private Map<Integer, String> getMappingVariables(
    Set<VariableSubstitutionDefinition> substitutions,
    Map<Event, Map<Attribute, String>> attributes,
    List<Condition> conditions
  ) {
    
    // Create set of all values present in the problem
    Set<Integer> distinctValues = new HashSet<>();
    Map<Integer, String> map = new HashMap<>();
    
    substitutions.forEach(x -> 
      distinctValues.addAll(x.substitutionValues)
    );
    attributes.values().forEach(x -> {
      x.values().forEach(y -> {
        y = y.replaceAll("[a-zA-Z]", ""); // UGLY!
        distinctValues.add(Integer.valueOf(y));
      });
    });
    conditions.forEach(x -> 
      distinctValues.add(x.value)
    );

    // Create variable names for each distinct value
    for (Integer value : distinctValues) {
      map.put(value, "v" + value);
    }
    
    return map;
  }

  private Map<Event, Map<Attribute, String>> parseEvents(ArrayList<Event> events) {
    
    int index = 0;
    Map<Event, Map<Attribute, String>> assignments = new HashMap<>();
    for(Event event : events) {
      event.setName("t" + index++); // Assign event name that will be put in the PDDL.
      if (index == events.size()) { // If last element
        State finalTraceState = new State("t" + index); // Last trace state is not in the trace, we will need to create it ourselves.
        this.finalTraceState = finalTraceState;
      }
      assignments.put(event, event.getAttributeAssignments());
    }
    return assignments;
  }

  private StringBuilder buildObjectsString(Map<Event, Map<Attribute, String>> attributeAssignments, Map<Integer, String> variables) {
    StringBuilder b = new StringBuilder();
    b.append("  (:objects\n");

    // TRACE STATES
    b.append("    ");
    attributeAssignments.keySet().forEach(x -> b.append(x.getName() + " "));
    b.append(this.finalTraceState.name + " ");
    b.append("- trace_state\n");


    // AUTOMATON STATES
    b.append("    ");
    this.constraintAutomatons.forEach(x -> {
      x.getStates().forEach(y -> {
        b.append(y.name + " ");
      });
    });
    b.append("- automaton_state\n");

    // ACTIVITIES
    b.append("    ");
    this.activities.keySet().forEach(x -> b.append(x + " "));
    b.append("- activity\n");

    // ATTRIBUTES
    Set<String> attributes = attributeAssignments.values()
      .stream()
      .flatMap(x -> x.keySet().stream())
      .map(x -> x.getName())
      .collect(Collectors.toSet());
    b.append("    ");
    attributes.forEach(x -> b.append(x + " "));
    b.append("- parameter_name\n");

    b.append("    ");
    variables.values().forEach(x -> b.append(x + " "));
    b.append("- variable_name\n");

    b.append("  )\n");
    return b;
  }

  private StringBuilder buildVariables(Map<Integer, String> variables, Set<VariableSubstitutionDefinition> substitutions) {
    StringBuilder b = new StringBuilder();

    b.append("  (:init\n\n");
    b.append("    ; Initialize plan cost. Some planners might need this explicitly\n");
    b.append("    (= (total_cost) 0)\n\n");
    b.append("    ;; VARIABLES\n");

    for (Map.Entry<Integer, String> entry : variables.entrySet()) {
      b.append("    (= (variable_value " + entry.getValue() + ") " + entry.getKey() + ")\n");
    }
    b.append("\n");
    for (VariableSubstitutionDefinition sub : substitutions) {

      for (Integer value : sub.substitutionValues) {
        b.append("    (has_substitution_value " 
          + sub.activityName + " " 
          + sub.categoryName + " " 
          + variables.get(value) 
          + ")\n");
      }
    }
    b.append("\n");

    return b;
  }
  private StringBuilder buildActionCosts(Map<Integer, String> variables) {
    StringBuilder b = new StringBuilder();
    b.append("    ; Action costs\n");

    for (Map.Entry<Pair<Activity, CostEnum>, Integer> cost : this.costs.entrySet()) {
      switch (cost.getKey().getValue()) {
        case CHANGE:
          b.append("    (change_cost " + cost.getKey().getKey().getName() + " " + variables.get(cost.getValue()) + ")\n");
          break;
        case ADD:
          b.append("    (add_cost " + cost.getKey().getKey().getName() + " " + variables.get(cost.getValue()) + ")\n");
          break;
        case SET:
          b.append("    (set_cost " + cost.getKey().getKey().getName() + " " + variables.get(cost.getValue()) + ")\n");
          break;
        case DELETE:
          b.append("    (delete_cost " + cost.getKey().getKey().getName() + " " + variables.get(cost.getValue()) + ")\n");
          break;
      }
    }
    b.append("\n");

    return b;
  }
  private StringBuilder buildTraceDeclaration(List<Event> events, Map<Event, Map<Attribute, String>> assignments, Map<Integer, String> variables) {
    StringBuilder b = new StringBuilder();
    b.append("    ;; TRACE DECLARATION\n");

    b.append("    (cur_t_state " + events.get(0).getName() + ")\n");
    Iterator<Event> it1 = events.iterator();
    Event cur;

    Iterator<Event> it2 = events.iterator();
    Event next;
    if (it2.hasNext()) {
      next = it2.next();
    }
    String activity;


    while (it1.hasNext()) {
      cur = it1.next();
      
      // If last element
      String nextName;
      if (!it2.hasNext()) {
        nextName = this.finalTraceState.name;
      } else { // if inside
        next = it2.next();
        nextName = next.getName();
      }

      activity = XConceptExtension.instance().extractName(cur.getXEvent());
      b.append("    (trace " + cur.getName() + " " + activity + " " + nextName + ")\n");
      for(Map.Entry<Attribute, String> singleAssignment : assignments.get(cur).entrySet()) {
        String value = singleAssignment.getValue();
        value = value.replaceAll("[a-zA-Z]", ""); // Remove chars, use as if numbers (in case of enum types)

        // NOTE With this definition, a trace parameter might be able to have more values for the same (activity, attribute) pair which is not senseful.
        // Be careful here.
        b.append("    (has_parameter " + activity + " " + singleAssignment.getKey().getName() + " " + cur.getName() + " " + nextName + ")\n");
        b.append("    (trace_parameter " + activity + " " + singleAssignment.getKey().getName() + " " + cur.getName() + " " + nextName + " " + variables.get(Integer.valueOf(value)) + ")\n");
        // b.append("    (= (trace_parameter " + activity + " " + singleAssignment.getKey().getName() + " " + cur.getName() + " " + nextName + ") " + value + ")\n");
      }
      b.append("\n");
    }

    return b;
  }

  public StringBuilder buildAutomatons(List<State> finalAutomatonStates, Map<Integer, String> variables) {
    StringBuilder b = new StringBuilder();
    b.append("    ;; AUTOMATON STATES\n");

    for (Automaton aut : this.constraintAutomatons) {
      
      for (State state : aut.getStates()) {
        if (state.isInitial) {
          b.append("    (cur_s_state " + state.name + ")\n");
        }
        if (state.isFailure) {
          b.append("    (failure_state " + state.name + ")\n");
        }
      }

      for (Transition t : aut.getTransitions()) {
        b.append("    (automaton " + t.getActiviationState().name + " " + t.getActivity() + " " + t.getTargetState().name + ")\n");

        List<Condition> conditions = t.getReformedConditions();
        if (conditions != null) {
          for (Condition c : conditions) {
            b.append(this.getConditionString(t, c, variables));
          }
        }
      }
    
      b.append("\n");
    }

    // Close init
    b.append("  )\n");
    return b;
  }
  private StringBuilder getConditionString(Transition t, Condition c, Map<Integer, String> variables) {
    StringBuilder b = new StringBuilder();

    if (c.operator == null) return b;

    switch (c.operator) {
      case BIGGER_OR_EQUAL:
        b.append("    (has_maj_c " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + " " + variables.get(c.value) + ")\n");
        // b.append("    (= (majority_constraint " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + ") " + c.value + ")\n");
        break;
      case LESS_OR_EQUAL:
        b.append("    (has_min_c " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + " " + variables.get(c.value) + ")\n");
        // b.append("    (= (minority_constraint " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + ") " + c.value + ")\n");
        break;
      case EQUAL:
        b.append("    (has_eq_c " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + " " + variables.get(c.value) + ")\n");
        // b.append("    (= (equality_constraint " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + ") " + c.value + ")\n");
        break;
      case NOT_EQUAL:
        b.append("    (has_ineq_c " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + " " + variables.get(c.value) + ")\n");
        // b.append("    (= (inequality_constraint " + c.activity + " " + c.parameterName + " " + t.getActiviationState().name + " " + t.getTargetState().name + ") " + c.value + ")\n");
        break;

      default:
        break;
    }

    return b;
  }
  private StringBuilder buildGoals() {
    StringBuilder b = new StringBuilder();

    b.append("  ;; GOAL STATES\n");
    b.append("  (:goal (and\n");

    b.append("    (cur_t_state " + this.finalTraceState.name + ")\n");
    for (List<State> goalStates : this.goalAutomatonStates) {
      if (goalStates.size() == 1) {
        b.append("    (cur_s_state " + goalStates.get(0).name + ")\n");
      } else { // In case two or more

        b.append("    (or\n");
        for (State singleGoal : goalStates) {
          b.append("      (cur_s_state " + singleGoal.name + ")\n");
        }
        b.append("    )\n");
      }
    }

    b.append("    (not (failure))\n" +
            "    (not (after_change))\n" + //
            "    (not (after_add))\n" + //
            "    (not (after_sync))\n" + //
            "  ))\n\n"
    );
    return b;
  }

  public String defineDomain(String domainWithPlaceholders) {

    // No placeholders to override yet!.
    return domainWithPlaceholders;
  }
}