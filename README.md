# numeric-PDDL_generator

This repository contains the Java code that is used to generate a numeric PDDL representation of event-traces (in .xes format) and Hybrid Business Process Representations (in .decl and .pnml format).

Results of the tests are also available.

## How to get started

The project relies on a very rigid folder structure.

All the source code is located under: pddl_gen/src/main/java
All the Input files used to generate the experiments are located under: pddl_gen/src/main/resources/input
All the generated files (problem instances) are located under: pddl_gen/src/main/resources/output

The project works with Java 17, although newer versions should work as well.

### Creating a runnable jar

The runnable jar for the project needs to be located under: pddl_gen/target/pddl_gen-1.0-SNAPSHOT-launcher.jar#

## Future Work

Here is a (non-exhaustive) list of things I would like to work on in the future

- Automate the creation of the variable mapping files (from the event log).
- Provide option for disabling vacuous satisfaction. Idea: provide an existance constraint for every activation condition in the model, such that the constraint cannot be vacuously satisfied.
- Select the different kind of encodings (go-to state, shared-states, etc...). Not sure if this will even help at all, but it's worth a try to also compare.
