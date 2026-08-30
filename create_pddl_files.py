import os
import sys
import subprocess
import time
import pm4py





input_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\input"
output_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\output\pddl"
#output_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\output\pddl"
cost_model = "cost_model.txt"
variable_values = "variable_values.txt"
#variable_values = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\input\variable_values.txt"


#cmd = r'java -jar '


if __name__ == "__main__":

    decl_path = os.path.join(input_path, "declare")
    pn_path = os.path.join(input_path, "petrinet")
    log_path = os.path.join(input_path, "logs")

    decl_f = os.listdir(decl_path)
    pn_f = os.listdir(pn_path)

    decl_f = [f for f in decl_f if f[-4:] == "decl"]
    pn_f = [f for f in pn_f if f[-4:] == "pnml"]

    pns = dict()
    logs = []

    if "cost_models" not in os.listdir(input_path):
        os.mkdir(os.path.join(input_path, "cost_models"))    
        for pn in pn_f:
            pm = pm4py.read_pnml(os.path.join(pn_path, pn))
            pnname = pn[:-5]
            with open(os.path.join(input_path, "cost_models", f"cost_model-{pnname}.txt"), "w+") as f:
                f.write("\n".join([t.label+" 1 2 1 2" for t in pm[0].transitions]))

    for p_ in pn_f:
        pname = p_[:-5]

        if not (os.path.exists(os.path.join(decl_path, pname))):
            continue
        
        declmods = os.listdir(os.path.join(decl_path, pname))

        # Does log exists?
        if not (os.path.exists(os.path.join(log_path, f"{pname}.xes"))):
            continue   

        for f in declmods:
            
            if f[-4:] != "decl" or ("parsed" not in f):
                continue

            #print(pname, f[-4:])

            var_sub_file = f.split("_parsed")[0]+".decl.txt"
            var_sub_file = f"variable_substitutions_{var_sub_file}"


            r'''
            decl_loc = f"declare\\{pname}\\{f}"
            pn_loc = f"petrinet\\{p_}"

            #"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\input\petrinet\BasePN-0And.pnml"
            log_loc = f"logs\\{pname}.xes"
            var_sub_loc = f"variable_subs/{var_sub_file}"

            decl_loc = f"pddl_gen\\src\\main\\resources\\input\\declare\\{pname}\\{f}"
            pn_loc = f"pddl_gen\\src\\main\\resources\\input\\petrinet\\{p_}"
            log_loc = f"pddl_gen\\src\\main\\resources\\input\\logs\\{pname}.xes"
            var_sub_loc = f"pddl_gen\\src\\main\\resources\\input\\variable_subs\\{var_sub_file}"


            noise_ = [0.1, 0.2, 0.3]
            all_logs = [
                #log_loc,
                #f"logs/{pname}-0.1.xesstripped.xes",
                #f"logs/{pname}-0.2.xesstripped.xes",
                #f"logs/{pname}-0.3.xesstripped.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-add-1.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-add-2.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-add-3.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-add-5.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-del-1.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-del-2.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-del-3.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-del-5.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-change-1.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-change-2.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-change-3.xes",
                f"pddl_gen\\src\\main\\resources\\input\\logs/{pname}-change-5.xes",

            ]
            '''

            decl_loc = f"declare\\{pname}\\{f}"
            pn_loc = f"petrinet\\{p_}"
            log_loc = f"logs\\{pname}.xes"
            var_sub_loc = f"variable_subs\\{var_sub_file}"

            all_logs = [
                f"logs/{pname}-add-1.xes",
                f"logs/{pname}-add-2.xes",
                f"logs/{pname}-add-3.xes",
                f"logs/{pname}-add-5.xes",
                f"logs/{pname}-del-1.xes",
                f"logs/{pname}-del-2.xes",
                f"logs/{pname}-del-3.xes",
                f"logs/{pname}-del-5.xes",
                f"logs/{pname}-change-1.xes",
                f"logs/{pname}-change-2.xes",
                f"logs/{pname}-change-3.xes",
                f"logs/{pname}-change-5.xes",

            ]


            for l in all_logs:
                #new_folder_name = f.replace("_parsed.decl", "").replace("_", "-d")
                #l = l.replace("logs/", f"pddl_gen\\src\\main\\resources\\input\\logs\\")
                
                
                if (len(l.split("/"))>1):
                    new_folder_name = l.split("/")[1]
                    new_folder_name = (new_folder_name+"-d"+(f.replace("_parsed.decl", "").replace("_", "-d").split("-d")[1])).replace(".xes", "")
                else:
                    new_folder_name = f.replace("_parsed.decl", "").replace("_", "-d")

                new_folder_path = os.path.join(output_path, new_folder_name)
                print(pname, f[-4:], new_folder_path)
                
                if not (os.path.exists(new_folder_path)):
                    os.mkdir(new_folder_path)
                    time.sleep(5)
                else:
                    continue

                cost_model = f"cost_models/cost_model-{pname}.txt"
                #cost_model = os.path.join(input_path, cost_model)
                print(['java', '-jar', r'C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\target\pddl_gen-1.0-SNAPSHOT-launcher.jar', decl_loc, pn_loc, l, variable_values, var_sub_loc, cost_model])
                subprocess.call(['java', '-jar', r'C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\target\pddl_gen-1.0-SNAPSHOT-launcher.jar', decl_loc, pn_loc, l, variable_values, var_sub_loc, cost_model])


                #output_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\output\pddl"
                #output_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\output\pddl"

                pddl_files = os.listdir(output_path)

                pddl_files = [pf for pf in pddl_files if pf[-4:] == "pddl" and "problem" in pf]

                [os.rename(os.path.join(output_path, pf), os.path.join(new_folder_path, pf)) for pf in pddl_files]
                
            
            #print(decl_loc, pn_loc, log_loc, var_sub_loc)
            
            #new_folder_name = f.replace("_parsed.decl", "").replace("_", "-d")
            #new_folder_path = os.path.join(output_path, new_folder_name)
            #if not (os.path.exists(new_folder_path)):
            #    os.mkdir(new_folder_path)
            #    time.sleep(5)
            #else:
            #    continue

            #subprocess.call(['java', '-jar', r'C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\target\pddl_gen-1.0-SNAPSHOT-launcher.jar', decl_loc, pn_loc, log_loc, variable_values, var_sub_loc, cost_model])


            #output_path = r"C:\Users\paulw\Desktop\numeric-PDDL_generator\pddl_gen\src\main\resources\output\pddl"

            #pddl_files = os.listdir(output_path)

            #pddl_files = [pf for pf in pddl_files if pf[-4:] == "pddl" and "problem" in pf]

            #[os.rename(os.path.join(output_path, pf), os.path.join(new_folder_path, pf)) for pf in pddl_files]


            
            print("-"*100)

        