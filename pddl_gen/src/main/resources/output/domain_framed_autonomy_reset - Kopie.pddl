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
    (automaton ?s1 - automaton_state ?a - activity ?s2 - automaton_state)
    (cur_t_state ?t - trace_state)
    (cur_s_state ?s - automaton_state)
    (goal_state ?s - automaton_state)
    (final_t_state ?t - trace_state)
    (violated ?c - constraint)
    (initial_state ?s1 - automaton_state) 
    
    (associated ?s1 - automaton_state ?c - constraint)
    (dummy ?s1 - automaton_state ?c - constraint ?s2 - automaton_state)

    ;; PARAMETER AND CONSTRAINT DECLARATION
    (has_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state)
    (has_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)

    ; Predicates to keep track of planner progress
    (invalid ?s1 - automaton_state ?a - activity ?s2 - automaton_state)
    (complete_sync ?a - activity)
    (after_sync)
    (after_add)
    (after_add_check)
    (after_change)
    (changed ?t1 - trace_state ?pn - parameter_name)
    (recovery_finished)

    ; Declare this to indicate that such activity-parameter-value assignment exists.
    (has_substitution_value ?vn - value_name ?a - activity ?pn - parameter_name)
    ; Indicates that the new activity has a new (defined) parameter.
    (has_added_parameter_aut ?a - activity ?par - parameter_name ?s1 - automaton_state)

    ; Used in the problem definition to indicate that this state must not be reached. In that case, the trace is **automatically** failed.
    (failure_state ?s - automaton_state)
    ; Used to indicate that the trace alignment couldn't possibly complete: prune -> less branching -> heap won't kaboom.
    (failure)

  )

  (:functions
    (total_cost)

    ; There exists a value connected to the activity that occures between the two trace states.
    (trace_parameter ?a - activity ?pn - parameter_name ?t1 - trace_state ?t2 - trace_state)
    (majority_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    (minority_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    (interval_constraint_lower ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    (interval_constraint_higher ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    (equality_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
    (inequality_constraint ?a - activity ?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)

    ;; VARIABLES SUBSTITUTION / ADDITION
    (variable_value ?var - value_name)
    (added_parameter_aut ?a - activity ?par - parameter_name ?s1 - automaton_state)
    ;;
    (violation_cost ?c - constraint)
  )

  ;; SUBSTITUTION
  ;; ----------------------------------------------------------------------------------------------------
  

  ;; ADDITION
  ;; Adding a parameter to a trace
  ;; ----------------------------------------------------------------------------------------------------
  ;; DELETION
  ;; ----------------------------------------------------------------------------------------------------
  

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
      (recovery_finished)

      (not (exists (?c - constraint) 
        (violated ?c)
      ))


      (exists (?s1 - automaton_state ?s2 - automaton_state) 
        (and
        
        (cur_s_state ?s1)
        (not (goal_state ?s1))
        (not (failure_state ?s1))
        
        (automaton ?s1 ?a ?s2)
        (not (failure_state ?s2))
        )
        )
      )
    :effect (and 
      (increase (total_cost) 0)
      (after_add)
      (complete_sync ?a)
  ))

  (:action move_in_model_parameter
      :parameters (?a - activity ?s1 - automaton_state ?pn - parameter_name ?vn - value_name)
      :precondition (and 
      (complete_sync ?a)
      (after_add)
      (has_substitution_value ?vn ?a ?pn)
      (cur_s_state ?s1)
      
      (not (goal_state ?s1))

      (not (has_added_parameter_aut ?a ?pn ?s1))
      (not (after_add_check))
      ; Only add a parameter if it is necessary
      ; And if it satisfies at least one guard
      (exists (?s2 - automaton_state) 
      (and
    
        (automaton ?s1 ?a ?s2)
        (has_constraint ?a ?pn ?s1 ?s2)
        (not (failure_state ?s2))
        (or
        (> (variable_value ?vn) (majority_constraint ?a ?pn ?s1 ?s2))
        (< (variable_value ?vn) (minority_constraint ?a ?pn ?s1 ?s2))

        (= (variable_value ?vn) (equality_constraint ?a ?pn ?s1 ?s2))
        (> (variable_value ?vn) (inequality_constraint ?a ?pn ?s1 ?s2))
        (< (variable_value ?vn) (inequality_constraint ?a ?pn ?s1 ?s2))

        )
        
      )
      )
      )

      :effect (and 

      (increase (total_cost) 0)
      (has_added_parameter_aut ?a ?pn ?s1)
      (assign (added_parameter_aut ?a ?pn ?s1) (variable_value ?vn)))
  )

  (:action check_added_variables_model
    :parameters (?a - activity)
    :precondition (and 
      (complete_sync ?a)
      (after_add)
      (not (after_add_check))

    )
    :effect (and 
      (after_add_check)
      (not (after_add))


      (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
          ;  ; If parameter is missing
            (when 

            (and 
           
            
            (cur_s_state ?s1)
            (automaton ?s1 ?a ?s2)
            (has_constraint ?a ?pn ?s1 ?s2)
            
            (or
            
            (not (has_added_parameter_aut ?a ?pn ?s1))
          
            (and 

            (has_added_parameter_aut ?a ?pn ?s1)
            (or 
            (< (added_parameter_aut ?a ?pn ?s1) (majority_constraint ?a ?pn ?s1 ?s2))
            (> (added_parameter_aut ?a ?pn ?s1) (minority_constraint ?a ?pn ?s1 ?s2))
            (< (added_parameter_aut ?a ?pn ?s1) (interval_constraint_lower ?a ?pn ?s1 ?s2))
            (> (added_parameter_aut ?a ?pn ?s1) (interval_constraint_higher ?a ?pn ?s1 ?s2))
            (< (added_parameter_aut ?a ?pn ?s1) (equality_constraint ?a ?pn ?s1 ?s2))
            (> (added_parameter_aut ?a ?pn ?s1) (equality_constraint ?a ?pn ?s1 ?s2))
            (= (added_parameter_aut ?a ?pn ?s1) (inequality_constraint ?a ?pn ?s1 ?s2))
            )
            )
            ))
              (invalid ?s1 ?a ?s2))
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
      (exists (?s1 - automaton_state ?s2 - automaton_state) 
      (and
        (not (goal_state ?s1))
        (not (invalid ?s1 ?a ?s2))
        (cur_s_state ?s1)
        (automaton ?s1 ?a ?s2)
        (not (failure_state ?s2)))
      )
      
      
      ; Ensure all inequality constraints for the added Action are fulfilled


      )
      :effect (and 
      (increase (total_cost) 0)
      (not (after_add_check))
      (forall (?s1 - automaton_state ?s2 - automaton_state)
        (when (and
          (automaton ?s1 ?a ?s2)
          (cur_s_state ?s1)
          (not (failure_state ?s2))
          (not (invalid ?s1 ?a ?s2))
          ) 
          (and
            (not (cur_s_state ?s1))
            (cur_s_state ?s2)
          )
        )
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

      (forall (?s1 - automaton_state ?pn - parameter_name)
            (when (has_added_parameter_aut ?a ?pn ?s1) (not (has_added_parameter_aut ?a ?pn ?s1)))
      )

      (forall (?s1 - automaton_state ?s2 - automaton_state)
        (when
          (and 
          (automaton ?s1 ?a ?s2)
          (invalid ?s1 ?a ?s2)
          )
          (not (invalid ?s1 ?a ?s2)) )
      )

      (not (complete_sync ?a))
  )
  )

  ;; SYNC OPERATIONS
  ;; ----------------------------------------------------------------------------------------------------
  ;; Action 'validate-payload' checks if the guards are satisfied
  ;; It sets all arcs that are "enabled" to '(not (invalid))',
  ;; and all disabled arcs to "invalid"
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

        (not (exists (?c - constraint) 
          (violated ?c)
        ))
        
        (not (recovery_finished))
        (exists (?s1 - automaton_state ?s2 - automaton_state ) 
        (and
        (cur_s_state ?s1)
        (not (failure_state ?s1))
        (not (goal_state ?s1))
        (automaton ?s1 ?a ?s2)
        (not (invalid ?s1 ?a ?s2))
        (not (failure_state ?s2))
       
        )
        )
        
        )
      :effect (and 
        (increase (total_cost) 0)
        (after_sync)
        (not (after_change))
        ;Check if case parameter is missing
        ;; The "nested" when seems to save time as we do not need to iterate 6+ times over all combinations
        (forall (?pn - parameter_name ?s1 - automaton_state ?s2 - automaton_state)
          ;  ; If parameter is missing
            (when 

            (and 
            ;(not (invalid ?s1 ?a ?s2))
            (cur_s_state ?s1)
            (automaton ?s1 ?a ?s2)
            (has_constraint ?a ?pn ?s1 ?s2)
            (or

            (not (has_parameter ?a ?pn ?t1 ?t2))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (majority_constraint ?a ?pn ?s1 ?s2))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (minority_constraint ?a ?pn ?s1 ?s2))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_lower ?a ?pn ?s1 ?s2))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (interval_constraint_higher ?a ?pn ?s1 ?s2))
            (< (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2))
            (> (trace_parameter ?a ?pn ?t1 ?t2) (equality_constraint ?a ?pn ?s1 ?s2))
            (= (trace_parameter ?a ?pn ?t1 ?t2) (inequality_constraint ?a ?pn ?s1 ?s2))
            )
            
            
            )
            
              (invalid ?s1 ?a ?s2))
          )      )
    )
  
  ;; Move automaton according to the enabled arcs decided in "validate-payload"
  (:action sync-actions
    :parameters (?t1 ?t2 - trace_state ?a - activity)
    :precondition (and 
      
      (not (after_add))
      (not (failure))
      (not (after_add_check))
      (not (complete_sync ?a))
      
      (after_sync)

      (cur_t_state ?t1)
      (trace ?t1 ?a ?t2)     
      
      ;(exists (?t1 ?t2 - trace_state) 
      ;(and (cur_t_state ?t1) 
      ;(trace ?t1 ?a ?t2)
      ;(not (final_t_state ?t1)))
      ;)

      (exists (?s1 - automaton_state ?s2 - automaton_state) 
        (and
        (cur_s_state ?s1)
        (not (goal_state ?s1))
        (not (failure_state ?s1))
        (automaton ?s1 ?a ?s2)
        (not (invalid ?s1 ?a ?s2))
        (not (failure_state ?s2))
        )
      )
      
 )

    :effect (and 
      (increase (total_cost) 0)


      (not (cur_t_state ?t1)) 
      (cur_t_state ?t2)
      (when (final_t_state ?t2) (recovery_finished))
      ;(forall (?t1 ?t2 - trace_state)
      ;  (and 
      ;  (when (and (cur_t_state ?t1) (trace ?t1 ?a ?t2)) 
      ;      (and (not (cur_t_state ?t1)) (cur_t_state ?t2) )
      ;  )
      ;  (when (and (cur_t_state ?t1) (trace ?t1 ?a ?t2) (final_t_state ?t2)) 
      ;;       (recovery_finished) )
      ;  )
      ;  )
      ;)

      (not (after_sync))
      
      ; Move all enabled automata that are ending in a valid state
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

      ; Move all enabled automata that are ending in a fail state
      (forall (?s1 - automaton_state ?s2 - automaton_state ?c - constraint)
        (when (and
          (not (invalid ?s1 ?a ?s2))
          (automaton ?s1 ?a ?s2)
          (cur_s_state ?s1)
          (failure_state ?s2)
          (associated ?s2 ?c)
        ) (and
          (not (cur_s_state ?s1))
          (cur_s_state ?s2)
          (failure)
          (violated ?c)
        ))
      )


      (forall (?s1 - automaton_state ?s2 - automaton_state) 
        (when (and 
          (invalid ?s1 ?a ?s2)
          (automaton ?s1 ?a ?s2)
          ) ; Without the when enclosing, it crashes.
          (not (invalid ?s1 ?a ?s2))
        )
      )
    )
  )


  (:action reset
      :parameters (?c - constraint)
      :precondition (and 
          (violated ?c)
          (failure))
      :effect (and 

      (increase (total_cost) 3)
      
      (forall (?s1 ?s2 - automaton_state)
        (when (and
            (cur_s_state ?s1)
            (failure_state ?s1)
            (initial_state ?s2)
            (dummy ?s1 ?c ?s2)
            )
            (and
            (not (cur_s_state ?s1))
            (cur_s_state ?s2)
            )  
        )
        )
      (not (failure))
      (not (violated ?c))
      )
  )

 (:action violate_pn
        :parameters (?e - activity)
        :precondition (and (not (failure))
        (not (after_sync))
        (not (after_add))
        
        (not (complete_sync ?e))
        (not (after_add_check))

        (exists (?s1 ?s2 - automaton_state) 
        (and
        (cur_s_state ?s1)
        (automaton ?s1 ?e ?s2))
        )
        
        ) 
        :effect(and
                    (forall (?s1 ?s2 - automaton_state ?c - constraint)
                        (and (when (and (cur_s_state ?s1) (automaton ?s1 ?e ?s2)) (and (not (cur_s_state ?s1)) (cur_s_state ?s2)))
                             (when (associated ?s2 ?c) (violated ?c))
                            
                        )
                    )

                    (forall (?t1 ?t2 - trace_state) 
                    (and
                    
                    (when 
                      (and
                        (trace ?t1 ?e ?t2)
                        (cur_t_state ?t1)
                        (not (final_t_state ?t2))
                      )
                      
                      (and
                      (not (cur_t_state ?t1))
                      (cur_t_state ?t2)
                      )
                    )

                    (when 
                    (and
                      (final_t_state ?t2)
                      (trace ?t1 ?e ?t2)
                      (cur_t_state ?t1)
                      )

                      
                      (and
                      (not (cur_t_state ?t1))
                      (cur_t_state ?t2)
                      (recovery_finished)
                      )
                    )
                    )
                    
                    )
                    
                    
                    
                    (failure)
                    (increase (total_cost) 3)
        )
                )
     

    (:action violate_decl
        :parameters (?s1 ?s2 - automaton_state ?e - constraint)
        :precondition (and 
            (not (failure))
            (cur_s_state ?s1)
            ;(failure_state ?s2) 

        (not (after_sync))
        (not (after_add))
        (not (failure))
        ;(not (complete_sync ?a))
        (not (after_add_check))
        
        (exists (?a - activity) 
        (and
        
        (automaton ?s1 ?a ?s2)
        (cur_s_state ?s1)
        )
        
        )
        ) 
        :effect(and

                (forall (?t1 ?t2 - trace_state ?a - activity)
                (and
                    (when 
                      (and
                        (trace ?t1 ?a ?t2)
                        (cur_t_state ?t1)
                        (not (final_t_state ?t2))
                      )
                      
                      (and
                        (not (cur_t_state ?t1))
                        (cur_t_state ?t2)
                      )
                    )

                    (when (and
                        (trace ?t1 ?a ?t2)
                        (cur_t_state ?t1)
                        (final_t_state ?t2)) 
                    
                        (and
                          (not (cur_t_state ?t1))
                          (cur_t_state ?t2)
                          (recovery_finished)
                        )
                    )
                )
                )
                    (not (cur_s_state ?s1)) (cur_s_state ?s2)
                    ;(when (and (is_sink ?s1) (blocked ?s1)) (not (blocked ?s1)))
                    (violated ?e) 
                    (increase (total_cost) 3)
                )
    ) 
  
  
)

