package Automaton;

import java.util.List;

public class VariableSubstitutionDefinition {
  public String activityName;
  public String categoryName;
  public List<Integer> substitutionValues;

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof VariableSubstitutionDefinition)) return false;

    VariableSubstitutionDefinition that = (VariableSubstitutionDefinition) o;
    if (!this.activityName.equals(that.activityName)) return false;
    if (!this.categoryName.equals(that.categoryName)) return false;
    if (!this.substitutionValues.equals(that.substitutionValues)) return false;

    return true;
  }
}
