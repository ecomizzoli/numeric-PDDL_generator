(define (domain trace-alignment)

  (:requirements :strips :typing :equality :adl :fluents :action-costs)

  (:types activity automaton_state trace_state parameter_name value_name constraint)

  ; ; Constants for prob
  ; (:constants
  ;   t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 - trace_state
  ;   s10 s11 s20 s21 s30 s31 s40 s41 s50 s51 s60 s61 s62 s70 s71 s72 s73 s80 s81 s82 - automaton_state
  ;   A B C D E F G - activity
  ;   x y z - parameter_name
  ;   a_x20 a_x40 a_y4 a_y6 a_z0 a_z1 c40 c30 c20 d10 d20 d40 e_x20 e_z0 e_z1 - value_name
  ; )

  ; ; Constants for prob2
  ; (:constants
  ;   t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 - trace_state
  ;   s10 s11 s20 s21 s30 s31 s40 s41 s50 s51 s52 s60 s61 s62 s70 s71 s80 s81 s100 s101 - automaton_state
  ;   a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 - activity
  ;   int cat - parameter_name
  ;   int5 int10 int15 cat1 cat2 cat3 - value_name
  ; )

  ;; Majority: >=
  ;; Minority: <=
  ;; Interval: [, ]
  ;; Equality: ==
  ;; Inequality: !=
  ;; If you want only > x, do conditions >= x && != x

  (:predicates 
    ;; TRACES AND AUTOMATONS
    (trace ?t1 - trace_state ?a - activity ?t2 - trace_state)
    (automaton ?s1 - automaton_state ?a - activity ?s2 - automaton_state ?e - constraint)
    (cur_t_state ?t - trace_state)
    (cur_s_state ?s - automaton_state ?e - constraint)
    (goal_state ?s - automaton_state ?e - constraint)

    ;; PARAMETER AND CONSTRAINT DECLARATION
    (has_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state)
    (has_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    ;(has_maj_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    ;(has_min_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    ;(has_interval_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    ;(has_eq_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    ;(has_ineq_c ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)

    ; Predicates to keep track of planner progress
    (invalid ?s1 - automaton_state ?a - activity ?s2 - automaton_state ?e - constraint)
    (complete_sync ?a - activity)
    (after_sync)
    ;(adding_value ?a - activity ?t1 - trace_state)
    ;(adding_value_model ?a - activity ?s1 - automaton_state)
    (after_add)
    (after_add_check)
    (after_change)
    (changed ?t1 - trace_state ?pn - parameter_name)

    ; Declare this to indicate that such activity-parameter-value assignment exists.
    (has_substitution_value ?vn - value_name ?a - activity ?pn - parameter_name)
    ; Indicates that the new activity has a new (defined) parameter.
    (has_added_parameter_aut ?a - activity ?par - parameter_name ?s1 - automaton_state ?e - constraint)

    ; Used in the problem definition to indicate that this state must not be reached. In that case, the trace is **automatically** failed.
    (failure_state ?s - automaton_state ?e - constraint)
    ; Used to indicate that the trace alignment couldn't possibly complete: prune -> less branching -> heap won't kaboom.
    (failure)

  )

  (:functions
    (total_cost)

    ; There exists a value connected to the activity that occures between the two trace states.
    (trace_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state)
    (majority_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    (minority_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    (interval_constraint_lower ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    (interval_constraint_higher ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    (equality_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
    (inequality_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)

    ;; VARIABLES SUBSTITUTION / ADDITION
    (variable_value ?var - value_name)
    (added_parameter_aut ?a - activity ?par - parameter_name ?s1 - automaton_state ?e - constraint)
    ;;
    (change_cost ?a - activity)
    (delete_cost ?a - activity)
    (set_cost ?a - activity)
    (add_cost ?a - activity)
  )

  ;; SUBSTITUTION
  ;; ----------------------------------------------------------------------------------------------------
  (:action change_value
    :parameters (?a - activity ?pn - parameter_name ?vn - value_name)
    :precondition (and 
      (exists (?t1 ?t2 - trace_state) 
      (and
        (trace ?t1 ?a ?t2)
        (cur_t_state ?t1)
        (has_parameter ?a ?pn ?t1 ?t2)
        (not (changed ?t1 ?pn))
      )
      )
    
      (has_substitution_value ?vn ?a ?pn)
     
      (not (after_sync))
      (not (after_add))
      (not (after_add_check))
      (not (failure))
      (not (complete_sync ?a))
      ;(not (after_change))
      

      
      (exists (?s1 ?s2 - automaton_state ?e - constraint) 
        (and
          (cur_s_state ?s1 ?e)
          
          (automaton ?s1 ?a ?s2 ?e)
          (has_constraint ?a ?pn ?s1 ?s2 ?e)
          
        )
      )

      
      ;(not (after_change))
    )
    :effect (and 
      (increase (total_cost) (change_cost ?a))
      (after_change)
      (forall (?t1 ?t2 - trace_state) 
      (when (and
        (trace ?t1 ?a ?t2)
        (cur_t_state ?t1)
        (has_parameter ?a ?pn ?t1 ?t2)
      ) (and
      (changed ?t1 ?pn)
      (assign (trace_parameter ?a ?pn ?t1 ?t2) (variable_value ?vn))
      )))
      
  ))

  ;; ADDITION
  ;; Adding a parameter to a trace
  ;; ----------------------------------------------------------------------------------------------------
  ;; DELETION
  ;; ----------------------------------------------------------------------------------------------------
  (:action del
    :parameters (?a - activity)
    :precondition (and 
    (exists (?t1 ?t2 - trace_state)
    (and
      (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2)
    )
    )

      (not (after_add))
      (not (complete_sync ?a))
      (not (after_sync)) 
      (not (after_add_check))
      (not (failure))
      (not (after_change))
    )
    :effect (and 
      (forall (?t1 ?t2 - trace_state)
      (when (and       (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2))
      (and       (not (cur_t_state ?t1)) 
      (cur_t_state ?t2))) )
      (increase (total_cost) (delete_cost ?a))

      )
  )

  ;; ADD ACTION / MOVE IN MODEL
  ;; add_action marks an activity A for addition
  ;; move_in_model_move_automata then moves all automata associated to the action A
  ;; --------------------------------------------------------------------------------------------------
    (:action add_action
    :parameters (?a - activity)
    :precondition (and 
      (not (after_add))
      (not (complete_sync ?a))
      (not (after_sync))
      (not (failure))
      (not (after_add_check))
      (not (after_change))
      (exists (?s1 - automaton_state ?s2 - automaton_state ?e - constraint) 
        (and
        
        (cur_s_state ?s1 ?e)
        (not (goal_state ?s1 ?e))
        (not (failure_state ?s1 ?e))
        
        (automaton ?s1 ?a ?s2 ?e)
        ;(goal_state ?s1)
        (not (failure_state ?s2 ?e))
        )
        )
      )
    :effect (and 
      (increase (total_cost) (add_cost ?a))
      (after_add)
      (complete_sync ?a)
  ))

  (:action move_in_model_parameter
      :parameters (?a - activity ?s1 - automaton_state ?pn - parameter_name ?vn - value_name ?e - constraint)
      :precondition (and 
      (complete_sync ?a)
      (after_add)
      (has_substitution_value ?vn ?a ?pn)
      (cur_s_state ?s1 ?e)
      
      (not (goal_state ?s1 ?e))

      (not (has_added_parameter_aut ?a ?pn ?s1 ?e))
      ;(not (after_sync))
      ;(not (failure))
      (not (after_add_check))
      ;(not (after_change))
      (exists (?s2 - automaton_state) 
      (and
    
        (automaton ?s1 ?a ?s2 ?e)
        (has_constraint ?a ?pn ?s1 ?s2 ?e)
        (not (failure_state ?s2 ?e))
        (or
        (> (variable_value ?vn) (majority_constraint ?a ?pn ?s1 ?s2 ?e))
        (< (variable_value ?vn) (minority_constraint ?a ?pn ?s1 ?s2 ?e))

        (= (variable_value ?vn) (equality_constraint ?a ?pn ?s1 ?s2 ?e))
        (> (variable_value ?vn) (inequality_constraint ?a ?pn ?s1 ?s2 ?e))
        (< (variable_value ?vn) (inequality_constraint ?a ?pn ?s1 ?s2 ?e))

        )
        
      )
      )
      )

      :effect (and 

      (increase (total_cost) (set_cost ?a))
      (has_added_parameter_aut ?a ?pn ?s1 ?e)
      (assign (added_parameter_aut ?a ?pn ?s1 ?e) (variable_value ?vn)))
  )

  (:action check_added_variables_model
    :parameters (?a - activity)
    :precondition (and 
      (complete_sync ?a)
      ;(not (failure))

      ;(not (after_sync))
      (after_add)
      (not (after_add_check))
      ;(not (after_change))
      
    )
    :effect (and 
      (after_add_check)
      (not (after_add))


      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
          ;  ; If parameter is missing
            (when 

            (and 
            ;(not (invalid ?s1 ?a ?s2))
            
            (cur_s_state ?s1 ?e)
            (automaton ?s1 ?a ?s2 ?e)
            (has_constraint ?a ?pn ?s1 ?s2 ?e)
            
            (or
            
            (not (has_added_parameter_aut ?a ?pn ?s1 ?e))
          
            (and 

            (has_added_parameter_aut ?a ?pn ?s1 ?e)
            (or 
            (< (added_parameter_aut ?a ?pn ?s1 ?e) (majority_constraint ?a ?pn ?s1 ?s2 ?e))
            (> (added_parameter_aut ?a ?pn ?s1 ?e) (minority_constraint ?a ?pn ?s1 ?s2 ?e))
            (< (added_parameter_aut ?a ?pn ?s1 ?e) (interval_constraint_lower ?a ?pn ?s1 ?s2 ?e))
            (> (added_parameter_aut ?a ?pn ?s1 ?e) (interval_constraint_higher ?a ?pn ?s1 ?s2 ?e))
            (< (added_parameter_aut ?a ?pn ?s1 ?e) (equality_constraint ?a ?pn ?s1 ?s2 ?e))
            (> (added_parameter_aut ?a ?pn ?s1 ?e) (equality_constraint ?a ?pn ?s1 ?s2 ?e))
            (= (added_parameter_aut ?a ?pn ?s1 ?e) (inequality_constraint ?a ?pn ?s1 ?s2 ?e))
            )
            )
            ))
              (invalid ?s1 ?a ?s2 ?e))
          )
      ; Check in case parameter is missing
      
    )
  )
  (:action move_in_model_move_automata
      :parameters (?a - activity)
      :precondition (and 
      ;(not (failure))
      ;(not (after_sync))
      (complete_sync ?a)
      (not (after_add))
      (after_add_check)
      ;(not (after_change))
      (exists (?s1 - automaton_state ?s2 - automaton_state ?e - constraint) 
      (and
        (not (goal_state ?s1 ?e))
        (not (invalid ?s1 ?a ?s2 ?e))
        (cur_s_state ?s1 ?e)
        (automaton ?s1 ?a ?s2 ?e)
        (not (failure_state ?s2 ?e)))
      )
      
      
      ; Ensure all inequality constraints for the added Action are fulfilled


      )
      :effect (and 
      (increase (total_cost) 0)
      (not (after_add_check))
      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
        (when (and
          (automaton ?s1 ?a ?s2 ?e)
          (cur_s_state ?s1 ?e)
          (not (failure_state ?s2 ?e))
          (not (invalid ?s1 ?a ?s2 ?e))
          ) 
          (and
            (not (cur_s_state ?s1 ?e))
            (cur_s_state ?s2 ?e)
          )
        )
      )
	  
      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
        (when (and
          (not (invalid ?s1 ?a ?s2 ?e))
          (automaton ?s1 ?a ?s2 ?e)
          (cur_s_state ?s1 ?e)
          (failure_state ?s2 ?e)
        ) (and
          (not (cur_s_state ?s1 ?e))
          (cur_s_state ?s2 ?e)
          (failure)    
        ))
      )

      (forall (?s1 - automaton_state ?pn - parameter_name ?e - constraint)
            (when (has_added_parameter_aut ?a ?pn ?s1 ?e) (not (has_added_parameter_aut ?a ?pn ?s1 ?e)))
      )

      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
        (when
          (and 
          (automaton ?s1 ?a ?s2 ?e)
          (invalid ?s1 ?a ?s2 ?e)
          )
          (not (invalid ?s1 ?a ?s2 ?e)) )
      )

      (not (complete_sync ?a))
  )
  )

  ;; SYNC OPERATIONS
  ;; ----------------------------------------------------------------------------------------------------
  ;; Action 'sync' checks if the guards are satisfied
  (:action validate-payload
      :parameters (?t1 - trace_state ?a - activity ?t2 - trace_state)
      :precondition (and 
        (cur_t_state ?t1) 
        (trace ?t1 ?a ?t2) 
        (not (after_sync))
        (not (after_add))
        (not (failure))
        (not (complete_sync ?a))
        (not (after_add_check))
        ;(exists (?s1 - automaton_state ?s2 - automaton_state ?pn - parameter_name)
        (exists (?s1 - automaton_state ?s2 - automaton_state ?e - constraint) 
        (and
        (cur_s_state ?s1 ?e)
        (not (failure_state ?s1 ?e))
        (not (goal_state ?s1 ?e))
        (automaton ?s1 ?a ?s2 ?e)
        (not (invalid ?s1 ?a ?s2 ?e))
        (not (failure_state ?s2 ?e))
        ;(or

            
        ;    (< (trace_parameter ?a ?pn ?t1 ?t2) (majority_constraint ?a ?pn ?s1 ?s2))
        ;    (> (trace_parameter ?a ?pn ?t1 ?t2) (minority_constraint ?a ?pn ?s1 ?s2))
        ;    (< (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_lower ?a ?pn ?s1 ?s2))
        ;    (> (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_higher ?a ?pn ?s1 ?s2))
        ;    (< (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2))
        ;    (> (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2))
        ;    (= (trace_parameter ?a ?pn ?t1 ?t2) (inequality_constraint ?a ?pn ?s1 ?s2))
        ;    )
        )
        )
        
        )
      :effect (and 
        (increase (total_cost) 0)
        (after_sync)
        (not (after_change))
        ;Check if case parameter is missing
        ;; The "nested" when seems to save time as we do not need to iterate 6+ times over all combinations
        (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
          ;  ; If parameter is missing
            (when 

            (and 
            ;(not (invalid ?s1 ?a ?s2))
            (cur_s_state ?s1 ?e)
            (automaton ?s1 ?a ?s2 ?e)
            (has_constraint ?a ?pn ?s1 ?s2 ?e)
            (or

            (not (has_parameter ?a ?pn ?t1 ?t2))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (majority_constraint ?a ?pn ?s1 ?s2 ?e))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (minority_constraint ?a ?pn ?s1 ?s2 ?e))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_lower ?a ?pn ?s1 ?s2 ?e))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_higher ?a ?pn ?s1 ?s2 ?e))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2 ?e))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2 ?e))
            (= (trace_parameter ?a ?pn ?t1 ?t2) (inequality_constraint ?a ?pn ?s1 ?s2 ?e))
            )
            
            
            )
            
              (invalid ?s1 ?a ?s2 ?e))
          )      )
    )
  
  ;; Move automaton
  (:action sync-actions
    :parameters (?a - activity)
    :precondition (and 
      ;(not (adding_value ?a ?t1))
      (not (after_add))
      (not (failure))
      (not (after_add_check))
      (not (complete_sync ?a))
      ;(not (after_change))
      (after_sync)
            
      ;(after_sync)
      (exists (?t1 ?t2 - trace_state) 
      (and (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2))
      )

      (exists (?s1 - automaton_state ?s2 - automaton_state ?e - constraint) 
        (and
        (cur_s_state ?s1 ?e)
        (not (goal_state ?s1 ?e))
        (not (failure_state ?s1 ?e))
        (automaton ?s1 ?a ?s2 ?e)
        (not (invalid ?s1 ?a ?s2 ?e))
        (not (failure_state ?s2 ?e))
        )
      )
      
 )

    :effect (and 
      (increase (total_cost) 0)
      (forall (?t1 ?t2 - trace_state)
      (when (and (cur_t_state ?t1) 
      (trace ?t1 ?a ?t2)
      ) 
      (and (not (cur_t_state ?t1)) 
      (cur_t_state ?t2)
      )
      )
      )

      (not (after_sync))
      
      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
        (when (and
          (not (invalid ?s1 ?a ?s2 ?e))
          (automaton ?s1 ?a ?s2 ?e)
          (cur_s_state ?s1 ?e)
          (not (failure_state ?s2 ?e))
        ) (and
          (not (cur_s_state ?s1 ?e))
          (cur_s_state ?s2 ?e)
        ))
      )


      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint)
        (when (and
          (not (invalid ?s1 ?a ?s2 ?e))
          (automaton ?s1 ?a ?s2 ?e)
          (cur_s_state ?s1 ?e)
          (failure_state ?s2 ?e)
        ) (and
          (not (cur_s_state ?s1 ?e))
          (cur_s_state ?s2 ?e)
          (failure)
        ))
      )

      (forall (?s1 - automaton_state ?s2 - automaton_state ?e - constraint) 
        (when (and 
          (invalid ?s1 ?a ?s2 ?e)
          (automaton ?s1 ?a ?s2 ?e)
          ) ; Without the when enclosing, it crashes.
          (not (invalid ?s1 ?a ?s2 ?e))
        )
      )
    )
  )
)
