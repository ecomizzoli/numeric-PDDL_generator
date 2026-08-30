
set -e # Exit on error
trap "echo 'Terminating...'; kill 0; exit 1" SIGINT

lengths=(5)		# length: 5, 10, 15, 20
models=(4_30)		# model: 2, 4, 6, 8
gen_path=pddl_gen
# gen_path=multi-perspective_aligner # if you want to test Axel Mezini's implementation. URL: https://github.com/axelmezini/multi-perspective_aligner
num_of_traces=200

echo "Running with following parameters:"
echo "gen_path=${gen_path}"
echo "num_of_traces=${num_of_traces}"

# Compile pddl generator if needed
cd $gen_path
mvn install
cd ..

cd java_helpers
javac StatsExtractor.java && jar cfe StatsExtractor.jar StatsExtractor StatsExtractor.class
cd ..

# echo "" > times.txt

# Find plan for all problems
for length in "${lengths[@]}"; do
  for model in "${models[@]}"; do
    echo "Now doing...";
    echo "length=${length}"
    echo "model=${model}"

    # Numeric PDDL files
     java -jar ${gen_path}/target/${gen_path}-1.0-SNAPSHOT-launcher.jar \
     	../input/models/model${model}.decl \
     	../input/traces${model}/${length}events_${model}.xes \
     	../input/variable_values.txt \
     	../input/variable_substitutions.txt \
     	../input/cost_model.txt

    # Propositionalized PDDL files
    # echo "Model: ${model}, length: ${length}" >> $results_file
    # /usr/bin/time -v java -jar ${gen_path}/target/${gen_path}-1.0-SNAPSHOT-launcher.jar \
    #   /models/model${model}.decl \
    #   /traces${model}/${length}events_${model}.xes \
    #   /cost_model.txt 2>&1 | tee -a $results_file

    results_file=results/${length}_${model}_dump.txt
    stats_file=results/${length}_${model}_stats.txt
    echo "" > $results_file

    for val in $(seq 1 $num_of_traces); do
      (wsl -e time -v java -Xmx64g -jar "//home/pwittlinger/WinDownloads/enhsp-20.jar" -o ${gen_path}/src/main/resources/output/pddl/domain.pddl -f ${gen_path}/src/main/resources/output/pddl/problem${val}.pddl -planner opt-blind) 2>&1 | tee -a $results_file

      # timeout 45 bash -c "/usr/bin/time -v ./ff -o ${gen_path}/src/main/resources/output/pddl/domain.pddl -f ${gen_path}/src/main/resources/output/pddl/problem${val}.pddl -s 3+H" 2>&1 | tee -a $results_file

      # (/usr/bin/time -v ./fast-downward-24.06.1/fast-downward.py ${gen_path}/src/main/resources/output/pddl/domain.pddl ${gen_path}/src/main/resources/output/pddl/problem${val}.pddl --search "astar(hmax())" ) 2>&1 | tee -a $results_file

      # timeout has precedence over /usr/bin/time, so nothing will be shown in that case
    done
    java -jar java_helpers/StatsExtractor.jar $results_file $stats_file $num_of_traces
  done
done

wait

