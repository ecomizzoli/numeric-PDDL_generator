(define (domain trace-alignment)

  (:requirements :strips :typing :equality :adl :fluents :action-costs)

  (:types activity automaton_state trace_state parameter_name variable_name)


  ;; Majority: >=
  ;; Minority: <=
  ;; Interval: [, ]
  ;; Equality: ==
  ;; Inequality: !=
  ;; If you want only > x, do conditions >= x && != x

  (:predicates 
    ;; TRACES AND AUTOMATONS
    (trace ?t1 - trace_state ?a - activity ?t2 - trace_state)
    (automaton ?s1 - automaton_state ?a - activity ?s2 - automaton_state)
    (cur_t_state ?t - trace_state)
    (cur_s_state ?s - automaton_state)

    ;; PARAMETER AND CONSTRAINT DECLARATION
    (has_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state)
    (trace_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state ?v - variable_name)

    (has_maj_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v - variable_name)
    (has_min_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v - variable_name)
    (has_interval_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?vl - variable_name ?vh - variable_name)
    (has_eq_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v - variable_name)
    (has_ineq_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v - variable_name)

    (invalid ?s1 - automaton_state ?a - activity ?s2 - automaton_state)
    (complete_sync ?a - activity)
    (after_sync)
    (after_change)
    (adding_value ?a - activity ?t1 - trace_state)
    (after_add)

    ; Declare this to indicate that such activity-parameter-value assignment exists.
    (has_substitution_value ?a - activity ?pn - parameter_name ?v - variable_name)
    ; Indicates that the new activity has a new (defined) parameter.
    (has_added_parameter ?a - activity ?par - parameter_name ?t1 - trace_state)
    (added_parameter ?a - activity ?par - parameter_name ?t1 - trace_state ?v - variable_name)

    ; Costs
    (change_cost ?a - activity ?v - variable_name)
    (add_cost ?a - activity ?v - variable_name)
    (set_cost ?a - activity ?v - variable_name)
    (delete_cost ?a - activity ?v - variable_name)

    ; Used in the problem definition to indicate that this state must not be reached. In that case, the trace is **automatically** failed.
    (failure_state ?s - automaton_state)
    ; Used to indicate that the trace alignment couldn't possibly complete: prune -> less branching -> heap won't kaboom.
    (failure)
  )

  (:functions
    (total_cost)

    ;; VARIABLES SUBSTITUTION / ADDITION
    (variable_value ?var - variable_name)
  )

  ;; SYNC OPERATIONS
  ;; ----------------------------------------------------------------------------------------------------
  (:action sync
    :parameters (?t1 - trace_state ?a - activity ?t2 - trace_state)
    :precondition (and 
      (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2) 
      (not (after_sync))
      (not (after_add))
      (not (failure)))
    :effect (and 
      (increase (total_cost) 0)
      (not (cur_t_state ?t1)) 
      (cur_t_state ?t2)
      (not (after_change))
      (after_sync)
      (complete_sync ?a)

      ; Check if case parameter is missing
      ; TODO Better forall?
      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If parameter is missing
        (when (and 
          (automaton ?s1 ?a ?s2)
          (not (has_parameter ?a ?pn ?t1 ?t2))
          (or
            (has_maj_c ?a ?pn ?s1 ?s2 ?v1)
            (has_min_c ?a ?pn ?s1 ?s2 ?v1)
            (has_interval_c ?a ?pn ?s1 ?s2 ?v1 ?v2)
            (has_eq_c ?a ?pn ?s1 ?s2 ?v1)
            (has_ineq_c ?a ?pn ?s1 ?s2 ?v1)
          ))
            (invalid ?s1 ?a ?s2))
      )

      ; Check for all conditions if a parameter is missing is not respecting a constraint
      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not >=has_parameter
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_parameter ?a ?pn ?t1 ?t2)
          (trace_parameter ?a ?pn ?t1 ?t2 ?v1)
          (has_maj_c ?a ?pn ?s1 ?s2 ?v2)
          (< (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not <=
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_parameter ?a ?pn ?t1 ?t2) 
          (trace_parameter ?a ?pn ?t1 ?t2 ?v1)
          (has_min_c ?a ?pn ?s1 ?s2 ?v2)
          (> (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name ?v3 - variable_name)
        ; If not [,]
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_parameter ?a ?pn ?t1 ?t2) 
          (trace_parameter ?a ?pn ?t1 ?t2 ?v1)
          (has_interval_c ?a ?pn ?s1 ?s2 ?v2 ?v3)
          (or
            (< (variable_value ?v1) (variable_value ?v2))
            (> (variable_value ?v2) (variable_value ?v3))
          ))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not =
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_parameter ?a ?pn ?t1 ?t2) 
          (trace_parameter ?a ?pn ?t1 ?t2 ?v1)
          (has_eq_c ?a ?pn ?s1 ?s2 ?v2)
          (or 
            (< (variable_value ?v1) (variable_value ?v2))
            (> (variable_value ?v1) (variable_value ?v2))
          ))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not !=
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_parameter ?a ?pn ?t1 ?t2) 
          (trace_parameter ?a ?pn ?t1 ?t2 ?v1)
          (has_ineq_c ?a ?pn ?s1 ?s2 ?v2)
          (= (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )
    )
  )

  (:action move_automatons
    :parameters (?a - activity)
    :precondition (and
      (not (after_change))
      (after_sync)
      (complete_sync ?a)
      (not (failure))
      (not (after_add))
    )
    :effect (and 
      (increase (total_cost) 0)
      (not (after_sync))
      (not (complete_sync ?a))

      (forall (?s1 - automaton_state ?s2 - automaton_state)
        (when (and
          (not (invalid ?s1 ?a ?s2))
          (automaton ?s1 ?a ?s2)
          (cur_s_state ?s1)
          (not (failure_state ?s2))
        ) (and
          (not (cur_s_state ?s1))
          (cur_s_state ?s2)
        ))
      )
      (forall (?s1 - automaton_state ?s2 - automaton_state)
        (when (and
          (not (invalid ?s1 ?a ?s2))
          (automaton ?s1 ?a ?s2)
          (cur_s_state ?s1)
          (failure_state ?s2)
        ) (and
          (not (cur_s_state ?s1))
          (cur_s_state ?s2)
          (failure)
        ))
      )

      ;; Clean invalid arcs. In case the same activity repeats, we might have different values and thus different invalid automatons.
      (forall (?s1 - automaton_state ?s2 - automaton_state) 
        (when (after_sync) ; Without the when enclosing, it crashes.
          (not (invalid ?s1 ?a ?s2))))
      )
  )

  ;; SUBSTITUTION
  ;; ----------------------------------------------------------------------------------------------------
  (:action change_value
    :parameters (?a - activity ?t1 - trace_state ?t2 - trace_state ?pn - parameter_name ?vn - variable_name)
    :precondition (and 
      (trace ?t1 ?a ?t2)
      (cur_t_state ?t1)
      (not (failure))
      (not (after_sync))
      (not (after_add))
      (has_substitution_value ?a ?pn ?vn)
      (has_parameter ?a ?pn ?t1 ?t2)
    )
    :effect (and 
      (after_change)

      ; Find cost
      (forall (?v - variable_name) 
        (when (change_cost ?a ?v)
          (increase (total_cost) (change_cost ?a ?v))
        )
      )

      ; Remove correct parameters
      (forall (?v - variable_name) 
        (when (trace_parameter ?a ?pn ?t1 ?t2 ?v)
          (not (trace_parameter ?a ?pn ?t1 ?t2 ?v))
        )
      )

      (has_parameter ?a ?pn ?t1 ?t2)
      (trace_parameter ?a ?pn ?t1 ?t2 ?vn)
  ))

  ;; ADDITION
  ;; ----------------------------------------------------------------------------------------------------
  (:action add
    :parameters (?a - activity ?t1 - trace_state)
    :precondition (and 
      (cur_t_state ?t1) 
      (not (after_change))
      (not (after_sync))
      (not (failure))
      (not (after_add))
    )
    :effect (and 

      ; Find cost
      (forall (?v - variable_name) 
        (when (add_cost ?a ?v)
          (increase (total_cost) (variable_value ?v))
        )
      )

      (adding_value ?a ?t1)
      (after_add)
  ))

  (:action set_value
    :parameters (?a - activity ?t1 - trace_state ?pn - parameter_name ?vn - variable_name)
    :precondition (and 
      (adding_value ?a ?t1)
      (cur_t_state ?t1)
      (not (failure))
      (not (after_change))
      (not (after_sync))
      (after_add)
      (has_substitution_value ?a ?pn ?vn)
      (not (has_added_parameter ?a ?pn ?t1))
    )
    :effect (and 

      ; Find cost
      (forall (?v - variable_name) 
        (when (set_cost ?a ?v)
          (increase (total_cost) (variable_value ?v))
        )
      )

      (has_added_parameter ?a ?pn ?t1)
      (added_parameter ?a ?pn ?t1 ?vn)
  ))

  (:action check_added_variables
    :parameters (?a - activity ?t1 - trace_state)
    :precondition (and 
      (adding_value ?a ?t1)
      (cur_t_state ?t1)
      (not (failure))
      (not (after_change))
      (not (after_sync))
      (after_add)
    )
    :effect (and 

      (not (adding_value ?a ?t1))
      (not (after_add))
      (after_sync)
      (complete_sync ?a)

      ; Check in case parameter is missing
      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If parameter is missing
        (when (and 
          (automaton ?s1 ?a ?s2)
          (not (has_added_parameter ?a ?pn ?t1))
          (or
            (has_maj_c ?a ?pn ?s1 ?s2 ?v1)
            (has_min_c ?a ?pn ?s1 ?s2 ?v1)
            (has_interval_c ?a ?pn ?s1 ?s2 ?v1 ?v2)
            (has_eq_c ?a ?pn ?s1 ?s2 ?v1)
            (has_ineq_c ?a ?pn ?s1 ?s2 ?v2)
          ))
            (invalid ?s1 ?a ?s2))
      )

      ; Check for all conditions if a parameter is missing is not respecting a constraint
      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not >=
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_added_parameter ?a ?pn ?t1)
          (added_parameter ?a ?pn ?t1 ?v1)
          (has_maj_c ?a ?pn ?s1 ?s2 ?v2)
          (< (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not <=
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_added_parameter ?a ?pn ?t1) 
          (added_parameter ?a ?pn ?t1 ?v1)
          (has_min_c ?a ?pn ?s1 ?s2 ?v2)
          (> (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name ?v3 - variable_name)
        ; If not [,]
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_added_parameter ?a ?pn ?t1) 
          (added_parameter ?a ?pn ?t1 ?v1)
          (has_interval_c ?a ?pn ?s1 ?s2 ?v2 ?v3)
          (or
            (< (variable_value ?v1) (variable_value ?v2))
            (> (variable_value ?v2) (variable_value ?v3))
          ))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not =
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_added_parameter ?a ?pn ?t1) 
          (added_parameter ?a ?pn ?t1 ?v1)
          (has_eq_c ?a ?pn ?s1 ?s2 ?v2)
          (or 
            (< (variable_value ?v1) (variable_value ?v2))
            (> (variable_value ?v1) (variable_value ?v2))
          ))
            (invalid ?s1 ?a ?s2))
      )

      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?v1 - variable_name ?v2 - variable_name)
        ; If not !=
        (when (and 
          (automaton ?s1 ?a ?s2)
          (has_added_parameter ?a ?pn ?t1) 
          (added_parameter ?a ?pn ?t1 ?v1)
          (has_ineq_c ?a ?pn ?s1 ?s2 ?v2)
          (= (variable_value ?v1) (variable_value ?v2)))
            (invalid ?s1 ?a ?s2))
      )
    )
  )

  ;; DELETION
  ;; ----------------------------------------------------------------------------------------------------
  (:action del
    :parameters (?t1 - trace_state ?a - activity ?t2 - trace_state)
    :precondition (and 
      (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2) 
      (not (after_change))
      (not (after_sync))
      (not (failure))
      (not (after_add))
    )
    :effect (and 

      ; Find cost
      (forall (?v - variable_name) 
        (when (delete_cost ?a ?v)
          (increase (total_cost) (variable_value ?v))
        )
      )

      (not (cur_t_state ?t1)) 
      (cur_t_state ?t2))
  )
)
