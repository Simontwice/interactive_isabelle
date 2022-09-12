from __future__ import print_function

import os
import json
import grpc
import sys

from copy import copy
from func_timeout import func_set_timeout, FunctionTimedOut
from typing import List

from pisa.src.main.python import server_pb2, server_pb2_grpc
from pathlib import Path
from typing import Optional


class EmptyInitialStateException(Exception):
    pass


class EnvInitFailedException(Exception):
    pass


class ProceedToLineFailedException(Exception):
    pass


class StepToTopLevelStateException(Exception):
    pass


class AvailableFactsExtractionError(Exception):
    pass


class AvailableFactsTimeout(Exception):
    pass


class _InactiveRpcError(Exception):
    pass


def trim_string_optional(input_string: Optional[str]) -> Optional[str]:
    if input_string is None:
        return None
    return " ".join(input_string.replace("\n", " ").split()).strip()


def premise_name_to_possible_isabelle_formats(premise_name):
    if any(
        [premise_name.endswith(f"_{i}") for i in range(40)]
    ):  # if the premise is of the form assms_1, which in Isabelle is actually assms(1)
        name_split = premise_name.split("_")
        prefix = "_".join(name_split[:-1])
        suffix = "(" + name_split[-1] + ")"
        possible_names = [prefix + suffix, premise_name]
    else:
        possible_names = [premise_name]
    return possible_names


def process_raw_global_facts(raw_string):
    # TODO: handle multiple facts with same name
    if raw_string == "":
        return {}
    if (
        raw_string
        == 'de.unruh.isabelle.control.IsabelleException: exception UNDEF raised (line 183 of "Isar/toplevel.ML")'
    ):
        raise AvailableFactsExtractionError
    list_of_string_tuples = raw_string.split("<SEP>")
    global_fact_dict = {}
    for element in list_of_string_tuples:
        name, definition = element.split("<DEF>")
        isabelle_possible_names = premise_name_to_possible_isabelle_formats(name)
        for possible_name in isabelle_possible_names:
            global_fact_dict[possible_name] = definition

    return global_fact_dict


MAX_MESSAGE_LENGTH = 10485760


class IsaFlexEnv:
    def __init__(
        self,
        port,
        isa_path,
        starter_string,
        working_directory,
    ):
        self.port = port
        self.isa_path = isa_path
        self.starter_string = starter_string
        self.working_directory = working_directory

        self.stub = None
        self.obs_string = None
        self.reset()

    def create_stub(self, port):
        MAX_MESSAGE_LENGTH = 1048576000
        self.channel = grpc.insecure_channel(
            "localhost:{}".format(port),
            options=[
                ("grpc.max_send_message_length", MAX_MESSAGE_LENGTH),
                ("grpc.max_receive_message_length", MAX_MESSAGE_LENGTH),
            ],
        )
        return server_pb2_grpc.ServerStub(self.channel)

    def observation(self):
        return self.obs_string

    def initialise_env(
        self, port, isa_path, theory_file_path=None, working_directory=None
    ):
        return IsaFlexEnv(
            port=port,
            isa_path=isa_path,
            starter_string=theory_file_path,
            working_directory=working_directory,
        )

    def is_finished(self, name_of_tls):
        returned_string = self.stub.IsabelleCommand(
            server_pb2.IsaCommand(command=f"<is finished> {name_of_tls}")
        ).state.strip()
        if returned_string.startswith("t"):
            return True
        else:
            return False

    @staticmethod
    def reward(done):
        return 1.0 if done else 0.0

    def reset(self):
        print(self.port)
        self.stub = self.create_stub(port=self.port)
        print("Hooray")
        try:
            print(self.stub.InitialiseIsabelle(server_pb2.IsaPath(path=self.isa_path)))
            print(
                self.stub.IsabelleWorkingDirectory(
                    server_pb2.IsaPath(path=self.working_directory)
                )
            )
            print(
                self.stub.IsabelleContext(
                    server_pb2.IsaContext(context=self.starter_string)
                )
            )
        except Exception as e:
            print(
                "Failure at initialising Isabelle process. "
                "Make sure the path your provide is where the Isabelle executable is."
            )
            print(e)
        return self.obs_string

    def get_proof_level(self, tls_name):
        proof_level = self.stub.IsabelleCommand(
            server_pb2.IsaCommand(command=f"<get_proof_level> {tls_name}")
        ).state
        return int(proof_level)

    def dependent_theorems(self, theorem_name):
        theorems = self.stub.IsabelleCommand(
            server_pb2.IsaCommand(command=f"<get_thm_deps> {theorem_name}")
        ).state
        return theorems.split("<SEP>")

    @func_set_timeout(20)
    def step_to_top_level_state(self, action, tls_name, new_name):
        # last_obs_string = self.stub.IsabelleCommand(server_pb2.IsaCommand(command=f"<get state> {tls_name}")).state
        try:
            obs_string = self.stub.IsabelleCommand(
                server_pb2.IsaCommand(
                    command=f"<apply to top level state> {tls_name} <apply to top level state> {action} <apply to top level state> {new_name}"
                )
            ).state
        except Exception as e:
            print("***Something went wrong***")
            print(e)

        done = self.is_finished(new_name)
        # done = True if ("subgoal" in last_obs_string and "subgoal" not in obs_string) else False
        return obs_string, self.reward(done), done, {}

    @func_set_timeout(200)
    def post(self, action):
        return self.stub.IsabelleCommand(server_pb2.IsaCommand(command=action)).state

    def extract_theory_steps(self):
        all_steps_str = self.stub.IsabelleCommand(
            server_pb2.IsaCommand(command="<extract_steps>")
        ).state
        list_of_steps = all_steps_str.split("<\\ISA_STEP>")
        list_of_useful_steps = []
        for step in list_of_steps:
            if not step.startswith("(*") and len(step) > 0:
                list_of_useful_steps.append(step)
        return list_of_useful_steps

    def clone_top_level_state(self, tls_name, old_name="default"):
        message = self.stub.IsabelleCommand(
            server_pb2.IsaCommand(command=f"<clone> {old_name} <clone> {tls_name}")
        ).state
        print(message)
        print(f"Cloned state called {tls_name}")

    ############################ THIS IS NEW, ADAPTED FROM ALBERT ##################################
    def local_facts(self, tls_name="default"):
        try:
            return self.post(f"<local facts and defs> {tls_name}")
        except:
            return "failed"

    def global_facts(self, tls_name="default"):
        try:
            facts = self.post(f"<global facts and defs> {tls_name}")
            return facts
        except FunctionTimedOut:
            raise AvailableFactsTimeout

    def all_facts_processed(self):
        _global = self.global_facts()
        _local = self.local_facts()

        processed_global = process_raw_global_facts(_global)
        processed_local = process_raw_global_facts(_local)
        processed_global.update(processed_local)
        processed_global = dict(
            filter(lambda key: not key[0].startswith("??"), processed_global.items())
        )

        return processed_global

    def find_thm(self, tls_name, thm_name):
        return self.stub.IsabelleCommand(
            server_pb2.IsaCommand(
                command=f"<find_thm> {tls_name} <find_thm> {thm_name}"
            )
        ).state

    def translate_premise_names(self, isabelle_state, premise_names: List[str]):
        """

        Args:
            premise_names: list of premise names of the form *_{n} for some natural n >= 1

        Returns:
            a corrected list of the names, where some _{n} are transformed to (n), as appropriate.
            It is possible that both _{n} and (n) are returned for some names.

        """
        corrected_premise_names: List[str] = []
        non_suspect_premises: List[str] = []
        for premise in premise_names:
            suffix = premise.split("_")[-1]
            prefix = premise.rsplit("_",1)[0]
            if suffix.isdigit():
                premise_alternative = f"{prefix}({suffix})"
                corrected_premise_names.append(premise_alternative)
                corrected_premise_names.append(premise)
            else:
                non_suspect_premises.append(premise)

        isa_steps = [f"using {premise}" for premise in corrected_premise_names]
        successful_steps: List[str] = []
        for step in isa_steps:

            next_proof_state, _, done, _ = self.step_to_top_level_state(
                step,
                isabelle_state.proof_state_id,
                -1,
            )

            next_proof_state_clean = trim_string_optional(next_proof_state)
            step_correct = next_proof_state_clean not in [None,"","Step error"]
            if step_correct:
                successful_steps.append(step)

        translated_premises = [step.split()[-1] for step in successful_steps]
        sus_and_nonsus_premises = translated_premises + non_suspect_premises

        return sus_and_nonsus_premises

    def destroy_isabelle(self):
        self.stub.IsabelleCommand(server_pb2.IsaCommand(command="exit"))
        self.channel.close()

    @func_set_timeout(200, allowOverride=True)
    def proceed_to_line(self, line_string, before_after):
        assert before_after in ["before", "after"]
        line_string = trim_string_optional(line_string)
        try:
            obs_string = self.stub.IsabelleCommand(
                server_pb2.IsaCommand(command=f"<proceed {before_after}> {line_string}")
            ).state
            return obs_string
        except _InactiveRpcError:
            raise ProceedToLineFailedException


def parsed_json_to_env_and_dict(
    path_to_json,
    afp_path,
    port=9000,
    isa_path="/Applications/Isabelle2020.app/Isabelle",
):
    save_dict = json.load(open(path_to_json))
    project = save_dict["project"]
    wd = os.path.join(afp_path, "thys", project)
    segments = save_dict["segments"]
    # Find starter string
    starter_string = None
    for line in segments:
        if line.strip().startswith("theory"):
            starter_string = " ".join(line.strip().split("\n"))
            break
    assert starter_string
    # print(port, isa_path, starter_string, wd, segments)
    return (
        IsaFlexEnv(
            port=port,
            isa_path=isa_path,
            starter_string=starter_string,
            working_directory=wd,
        ),
        save_dict,
    )


@func_set_timeout(300, allowOverride=True)
def initialise_env(port, isa_path, theory_file_path=None, working_directory=None):
    print(f"theory_file_path = {theory_file_path}")
    if working_directory is None:
        actual_working_dir_candidate = str(Path(theory_file_path).parents[0])
        i = 0
        success = False
        while not success and i < 5:
            try:
                env = IsaFlexEnv(
                    port=port,
                    isa_path=isa_path,
                    starter_string=theory_file_path,
                    working_directory=actual_working_dir_candidate,
                )
                success = True
            except:
                actual_working_dir_candidate = str(
                    Path(actual_working_dir_candidate).parents[0]
                )
                i += 1
        if success:
            print(
                f"Automatically detected working directory: {actual_working_dir_candidate}"
            )
        else:
            print(
                f"Did not manage to detect working directory: {actual_working_dir_candidate}"
            )
            raise ConnectionAbortedError
    return env


def initialise_problem(env, problem_name):
    env.proceed_to_line(problem_name, "after")
    return env


if __name__ == "__main__":
    env = initialise_env(
        8000,
        working_directory="/Applications/Isabelle2021.app/src/HOL/Examples",
        isa_path="/Applications/Isabelle2021.app",
        theory_file_path="/Applications/Isabelle2021.app/src/HOL/Examples/Adhoc_Overloading_Examples.thy",
    )
    print(env.post("<get_ancestors>"))
