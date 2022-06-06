package pisa.server

import util.control.Breaks
import scala.collection.mutable.ListBuffer
import _root_.java.nio.file.{Files, Path}
import _root_.java.io.File
import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.{AdHocConverter, MLFunction, MLFunction0, MLFunction2, MLFunction3, MLValue, MLValueWrapper}
import de.unruh.isabelle.mlvalue.MLValue.{compileFunction, compileFunction0, compileValue}
import de.unruh.isabelle.pure.{Context, Position, Theory, TheoryHeader, ToplevelState}
import pisa.utils.TheoryManager
import pisa.utils.TheoryManager.{Ops, Source, Text}

import scala.concurrent.{Await, ExecutionContext, Future, TimeoutException}
import scala.concurrent.duration.Duration

import sys.process._

// Implicits
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._

object Transition extends AdHocConverter("Toplevel.transition")

object ProofState extends AdHocConverter("Proof.state")

object RuntimeError extends AdHocConverter("Runtime.error")

object Pretty extends AdHocConverter("Pretty.T")

object ProofContext extends AdHocConverter("Proof_Context.T")

class PisaOS(var path_to_isa_bin: String, var path_to_file: String, var working_directory: String, var use_Sledgehammer: Boolean = false) {
  val currentTheoryName: String = path_to_file.split("/").last.replace(".thy", "")
  val currentProjectName: String = {
    if (path_to_file.contains("afp")) {
      working_directory.slice(working_directory.indexOf("thys/") + 5, working_directory.length).split("/").head
    } else if (path_to_file.contains("Isabelle") && path_to_file.contains("/src/")) {
      // The theory file could be /Applications/Isabelle2021.app/Isabelle/src/HOL/Analysis/ex
      // The correct project name for it is HOL-Analysis-ex
      val relative_working_directory =
      working_directory.slice(working_directory.indexOf("/src/") + 5, working_directory.length).split(
        "/")
      relative_working_directory.mkString("-")
    } else if (path_to_file.contains("miniF2F")) {
      //      working_directory.split("/").last
      "HOL"
    } else {
      "This is not supported at the moment"
    }
  }

  // Figure out the session roots information and import the correct libraries
  val sessionRoots: Seq[Path] = {
    if (path_to_file.contains("afp")) {
      Seq(Path.of(working_directory.slice(-1, working_directory.indexOf("thys/") + 4)))
    } else if (path_to_file.contains("Isabelle") && path_to_file.contains("/src/")) {
      val src_index: Int = working_directory.indexOf("/src/") + 5
      val session_root_path_string: String = working_directory.slice(0, src_index) +
        working_directory.slice(src_index, working_directory.length).split("/").head
      Seq(Path.of(session_root_path_string))
    } else if (path_to_file.contains("miniF2F")) {
      Seq()
    } else {
      Seq(Path.of("This is not supported at the moment"))
    }
  }

  // Prepare setup config and the implicit Isabelle context
  val setup: Isabelle.Setup = Isabelle.Setup(
    isabelleHome = Path.of(path_to_isa_bin),
    sessionRoots = sessionRoots,
    userDir = None,
    logic = currentProjectName,
    workingDirectory = Path.of(working_directory),
    build = false
  )
  implicit val isabelle: Isabelle = new Isabelle(setup)
  implicit val ec: ExecutionContext = ExecutionContext.global

  // Complie useful ML functions
  val script_thy: MLFunction2[String, Theory, Theory] = compileFunction[String, Theory, Theory]("fn (str,thy) => Thy_Info.script_thy Position.none str thy")
  val init_toplevel: MLFunction0[ToplevelState] = compileFunction0[ToplevelState]("Toplevel.init_toplevel")
  val is_proof: MLFunction[ToplevelState, Boolean] = compileFunction[ToplevelState, Boolean]("Toplevel.is_proof")
  val is_skipped_proof: MLFunction[ToplevelState, Boolean] = compileFunction[ToplevelState, Boolean]("Toplevel.is_skipped_proof")
  val proof_level: MLFunction[ToplevelState, Int] = compileFunction[ToplevelState, Int]("Toplevel.level")
  val proof_of: MLFunction[ToplevelState, ProofState.T] = compileFunction[ToplevelState, ProofState.T]("Toplevel.proof_of")
  val command_exception: MLFunction3[Boolean, Transition.T, ToplevelState, ToplevelState] = compileFunction[Boolean, Transition.T, ToplevelState, ToplevelState](
    "fn (int, tr, st) => Toplevel.command_exception int tr st")
  val command_errors: MLFunction3[Boolean, Transition.T, ToplevelState, (List[RuntimeError.T], Option[ToplevelState])] = compileFunction[Boolean, Transition.T, ToplevelState, (List[RuntimeError.T], Option[ToplevelState])](
    "fn (int, tr, st) => Toplevel.command_errors int tr st")
  val toplevel_end_theory: MLFunction[ToplevelState, Theory] = compileFunction[ToplevelState, Theory]("Toplevel.end_theory Position.none")
  val theory_of_state: MLFunction[ToplevelState, Theory] = compileFunction[ToplevelState, Theory]("Toplevel.theory_of")
  val context_of_state: MLFunction[ToplevelState, Context] = compileFunction[ToplevelState, Context]("Toplevel.context_of")
  val name_of_transition: MLFunction[Transition.T, String] = compileFunction[Transition.T, String]("Toplevel.name_of")
  val parse_text: MLFunction2[Theory, String, List[(Transition.T, String)]] = compileFunction[Theory, String, List[(Transition.T, String)]](
    """fn (thy, text) => let
      |  val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
      |  fun addtext symbols [tr] =
      |        [(tr, implode symbols)]
      |    | addtext _ [] = []
      |    | addtext symbols (tr::nextTr::trs) = let
      |        val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
      |        in (tr, implode this) :: addtext rest (nextTr::trs) end
      |  in addtext (Symbol.explode text) transitions end""".stripMargin)
  val theoryName: MLFunction2[Boolean, Theory, String] = compileFunction[Boolean, Theory, String](
    "fn (long, thy) => Context.theory_name' {long=long} thy")
  val ancestorsNamesOfTheory: MLFunction[Theory, List[String]] = compileFunction[Theory, List[String]](
    "fn (thy) => map Context.theory_long_name (Context.ancestors_of thy)"
  )
  val toplevel_string_of_state: MLFunction[ToplevelState, String] = compileFunction[ToplevelState, String](
    "Toplevel.string_of_state")
  val pretty_local_facts: MLFunction2[ToplevelState, Boolean, List[Pretty.T]] = compileFunction[ToplevelState, Boolean, List[Pretty.T]](
    "fn (tls, b) => Proof_Context.pretty_local_facts b (Toplevel.context_of tls)"
  )
  val make_pretty_list_string_list: MLFunction[List[Pretty.T], List[String]] = compileFunction[List[Pretty.T], List[String]](
    "fn (pretty_list) => map Pretty.unformatted_string_of pretty_list"
  )
  val header_read: MLFunction2[String, Position, TheoryHeader] =
    compileFunction[String, Position, TheoryHeader]("fn (text,pos) => Thy_Header.read pos text")

  // setting up Sledgehammer
  val thy_for_sledgehammer: Theory = Theory("HOL.List")
  val Sledgehammer_Commands: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Commands")
  val Sledgehammer: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer")
  val Sledgehammer_Prover: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Prover")
  val check_with_Sledgehammer: MLFunction[ToplevelState, Boolean] = compileFunction[ToplevelState, Boolean](
    s""" fn state =>
       |    (
       |    let
       |      val ctxt = Toplevel.context_of state;
       |      val thy = Proof_Context.theory_of ctxt
       |      val p_state = Toplevel.proof_of state;
       |      val params = ${Sledgehammer_Commands}.default_params thy
       |                      [("isar_proofs", "false"),("smt_proofs", "true"),("learn","true")]
       |      val override = {add=[],del=[],only=false}
       |      val run_sledgehammer = ${Sledgehammer}.run_sledgehammer params ${Sledgehammer_Prover}.Auto_Try
       |                                  NONE 1 override
       |                                : Proof.state -> bool * (string * string list);
       |    in
       |      run_sledgehammer p_state |> fst
       |    end)
    """.stripMargin)


  val local_facts_and_defs: MLFunction[ToplevelState, List[(String, String)]] =
    compileFunction[ToplevelState, List[(String, String)]](
      """fn tls =>
        |  let val ctxt = Toplevel.context_of tls;
        |      val facts = Proof_Context.facts_of ctxt;
        |      val props = map #1 (Facts.props facts);
        |      val local_facts =
        |        (if null props then [] else [("unnamed", props)]) @
        |        Facts.dest_static true [Global_Theory.facts_of (Proof_Context.theory_of ctxt)] facts;
        |      val thms = (
        |           if null local_facts then []
        |           else
        |           (map (fn e => #2 (#2 e)) (sort_by (#1 o #2) (map (`(Proof_Context.pretty_fact ctxt)) local_facts))));
        |      val condensed_thms = fold (fn x => fn y => (x @ y)) thms [];
        |  in
        |      map (fn thm => (
        |            Thm.get_name_hint thm,
        |            Pretty.unformatted_string_of
        |          (Element.pretty_statement ctxt "" thm)
        |         ))
        |         condensed_thms
        |  end""".stripMargin
    )
  val global_facts_and_defs: MLFunction[ToplevelState, List[(String, String)]] =
    compileFunction[ToplevelState, List[(String, String)]](
      """fn tls =>
        | map (fn tup => (#1 tup, Pretty.unformatted_string_of (Element.pretty_statement (Toplevel.context_of tls) "test" (#2 tup))))
        | (Global_Theory.all_thms_of (Proof_Context.theory_of (Toplevel.context_of tls)) false)
        """.stripMargin
    )
  def local_facts_and_defs_string(tls: ToplevelState): String =
    local_facts_and_defs(tls).force.retrieveNow.distinct.map(x => x._1 + "<DEF>" + x._2).mkString("<SEP>")
  def local_facts_and_defs_string(tls_name: String): String = {
    val tls = retrieve_tls(tls_name)
    try {
      local_facts_and_defs_string(tls)
    } catch {
      case e: Throwable => e.toString
    }
  }
  def global_facts_and_defs_string(tls: ToplevelState): String =
    global_facts_and_defs(tls).force.retrieveNow.distinct.map(x => x._1 + "<DEF>" + x._2).mkString("<SEP>")
  def global_facts_and_defs_string(tls_name: String): String = {
    val tls = retrieve_tls(tls_name)
    try {
      global_facts_and_defs_string(tls)
    } catch {
      case e: Throwable => e.toString
    }
  }


//  def total_facts(tls: ToplevelState): String = {
//    try {
//       val local_facts = local_facts_retriever(tls).force.retrieveNow
////      val local_facts = local_facts_and_defs(tls).force.retrieveNow
////        val global_facts = global_facts_and_defs(tls).force.retrieveNow
//    }
//
//    catch {
//      case ex : Exception => {
//        println ("\n" + ex)
//        println ("\n" + ex.getStackTrace + "\n")
//      }
//    }


//    val local_facts = local_facts_and_defs(toplevel).force.retrieveNow
//    val global_facts = global_facts_and_defs(toplevel).force.retrieveNow


//    catch {
//      case ex: Exception => {
//        println("\n" + ex)
//        println("\n" + ex.getStackTrace + "\n")
//      }
//    }

//    (local_facts ++ global_facts).distinct.map(x => x._1 + "<DEF>" + x._2).mkString("<SEP>")
//  }

  def all_local_facts(tls: ToplevelState): String = {
    println("toplevel:")
    print(getStateString)
    val local_facts = local_facts_and_defs(tls).force.retrieveNow
    local_facts.distinct.map(x => x._1 + "<DEF>" + x._2).mkString("<SEP>")
  }

  def all_global_facts(tls: ToplevelState): String = {
    val global_facts = global_facts_and_defs(tls).force.retrieveNow
    global_facts.distinct.map(x => x._1 + "<DEF>" + x._2).mkString("<SEP>")
  }

  // prove_with_Sledgehammer is mostly identical to check_with_Sledgehammer except for that when the returned Boolean is true, it will 
  // also return a non-empty list of Strings, each of which contains executable commands to close the top subgoal. We might need to chop part of 
  // the string to get the actual tactic. For example, one of the string may look like "Try this: by blast (0.5 ms)".
  val prove_with_Sledgehammer: MLFunction[ToplevelState, (Boolean, List[String])] = compileFunction[ToplevelState, (Boolean, List[String])](
    s""" fn state =>
       |    (
       |    let
       |      val ctxt = Toplevel.context_of state;
       |      val thy = Proof_Context.theory_of ctxt;
       |      val p_state = Toplevel.proof_of state;
       |      val params = ${Sledgehammer_Commands}.default_params thy
       |                      [("provers", "cvc4 e spass vampire z3"),("isar_proofs", "false"),("smt_proofs", "true"),("learn","true")]
       |      val override = {add=[],del=[],only=false}
       |      val run_sledgehammer = ${Sledgehammer}.run_sledgehammer params ${Sledgehammer_Prover}.Auto_Try
       |                                  NONE 1 override
       |                                : Proof.state -> bool * (string * string list);
       |    in
       |      run_sledgehammer p_state |> (fn (x, (_ , y)) => (x,y))
       |    end)
    """.stripMargin)

  def get_theory_ancestors_names(theory: Theory): List[String] = ancestorsNamesOfTheory(theory).force.retrieveNow

  def beginTheory(source: Source)(implicit isabelle: Isabelle, ec: ExecutionContext): Theory = {
    val header = getHeader(source)
    val masterDir = source.path
    val registers: ListBuffer[String] = new ListBuffer[String]()
    for (theory_name <- header.imports) {
      if (importMap.contains(theory_name)) {
        registers += s"${currentProjectName}.${importMap(theory_name)}"
      } else registers += theory_name
    }
    Ops.begin_theory(masterDir, header, registers.toList.map(Theory.apply)).retrieveNow
  }

  def getHeader(source: Source)(implicit isabelle: Isabelle, ec: ExecutionContext): TheoryHeader = source match {
    case Text(text, path, position) => Ops.header_read(text, position).retrieveNow
  }

  // Find out about the starter string
  private val fileContent: String = Files.readString(Path.of(path_to_file))

  private def getStarterString: String = {
    val decoyThy: Theory = Theory("Main")
    for ((transition, text) <- parse_text(decoyThy, fileContent).force.retrieveNow) {
      if (text.contains("theory") && text.contains(currentTheoryName) && text.contains("begin")) {
        return text
      }
    }
    "This is wrong!!!"
  }

  val starter_string: String = getStarterString.trim.replaceAll("\n", " ").trim

  // Find out what to import from the current directory
  def getListOfTheoryFiles(dir: File): List[File] = {
    if (dir.exists && dir.isDirectory) {
      var listOfFilesBuffer: ListBuffer[File] = new ListBuffer[File]
      for (f <- dir.listFiles()) {
        if (f.isDirectory) {
          listOfFilesBuffer = listOfFilesBuffer ++ getListOfTheoryFiles(f)
        } else if (f.toString.endsWith(".thy")) {
          listOfFilesBuffer += f
        }
      }
      listOfFilesBuffer.toList
    } else {
      List[File]()
    }
  }

  def sanitiseInDirectoryName(fileName: String): String = {
    fileName.replace("\"", "").split("/").last.split(".thy").head
  }

  // Figure out what theories to import
  val available_files: List[File] = getListOfTheoryFiles(new File(working_directory))
  var available_imports_buffer: ListBuffer[String] = new ListBuffer[String]
  for (file_name <- available_files) {
    if (file_name.getName().endsWith(".thy")) {
      available_imports_buffer = available_imports_buffer += file_name.getName().split(".thy")(0)
    }
  }
  var available_imports: Set[String] = available_imports_buffer.toSet
  val theoryNames: List[String] = starter_string.split("imports")(1).split("begin")(0).split(" ").map(_.trim).filter(_.nonEmpty).toList
  var importMap: Map[String, String] = Map()
  for (theoryName <- theoryNames) {
    val sanitisedName = sanitiseInDirectoryName(theoryName)
    if (available_imports(sanitisedName)) {
      importMap += (theoryName.replace("\"", "") -> sanitisedName)
    }
  }

  var top_level_state_map: Map[String, MLValue[ToplevelState]] = Map()
  val theoryStarter: TheoryManager.Text = TheoryManager.Text(starter_string, setup.workingDirectory.resolve(""))
  var thy1: Theory = beginTheory(theoryStarter)
  thy1.await
  var toplevel: ToplevelState = init_toplevel().force.retrieveNow

  def reset_map(): Unit = {
    top_level_state_map = Map()
  }

  def reset_prob(): Unit = {
    thy1 = beginTheory(theoryStarter)
    toplevel = init_toplevel().force.retrieveNow
    reset_map()
  }

  def getFacts(stateString: String): String = {
    var facts: String = ""
    if (stateString.trim.nonEmpty) {
      // Limit the maximum number of local facts to be 5
      for (fact <- make_pretty_list_string_list(pretty_local_facts(toplevel, false)).retrieveNow.takeRight(5)) {
        facts = facts + fact + "<\\PISASEP>"
      }
    }
    facts
  }

  def getStateString(top_level_state: ToplevelState): String =
    toplevel_string_of_state(top_level_state).retrieveNow

  def getStateString: String = getStateString(toplevel)

  def is_done(top_level_state: ToplevelState): Boolean = {
    getProofLevel(top_level_state) == 0
  }

  def getProofLevel(top_level_state: ToplevelState): Int =
    proof_level(top_level_state).retrieveNow

  def getProofLevel: Int = getProofLevel(toplevel)

  def singleTransition(single_transition: Transition.T, top_level_state: ToplevelState): ToplevelState = {
    command_exception(true, single_transition, top_level_state).retrieveNow.force
  }

  def singleTransition(singTransition: Transition.T): String = {
    //    TODO: inlcude global facts
    toplevel = singleTransition(singTransition, toplevel)
    getStateString
  }

  def singleTransitionWithSledgehammer(): (String, String) = {
    // Returns two strings, the first one being the real proof step, the second one being the new state string
    val raw_hammer_strings = prove_with_hammer(toplevel)._2
    var found = false
    var real_string = ""
    for (attempt_string <- raw_hammer_strings) {
      if (!found && (attempt_string contains "Try this:")) {
        found = true
        real_string = attempt_string.trim.stripPrefix("Try this:").trim.split('(').dropRight(1).mkString("(")
      }
    }
    toplevel = step(real_string, toplevel, 30000)
    (real_string, getStateString(toplevel))
  }

  def parseStateAction(isarString: String): String = {
    // Here we directly apply transitions to the theory repeatedly
    // to get the (last_observation, action, observation, reward, done) tuple
    var stateActionTotal: String = ""
    val continue = new Breaks
    // Initialising the state string
    var stateString = getStateString
    var proof_level_number = getProofLevel
    Breaks.breakable {
      for ((transition, text) <- parse_text(thy1, isarString).force.retrieveNow)
        continue.breakable {
          if (text.trim.isEmpty) continue.break
          else if (text.trim == "sledgehammer") {
            val current_state_string = stateString
            val current_proof_level = getProofLevel
            val (real_step, new_state_string) = singleTransitionWithSledgehammer()
            stateString = new_state_string
            stateActionTotal = stateActionTotal + (current_state_string + "<\\STATESEP>" + real_step.trim + "<\\STATESEP>" + s"$current_proof_level" + "<\\TRANSEP>")
          } else {
            stateActionTotal = stateActionTotal + (stateString + "<\\STATESEP>" + text.trim + "<\\STATESEP>" + s"$getProofLevel" + "<\\TRANSEP>")
            stateString = singleTransition(transition)
          }
        }
    }
    stateActionTotal
  }

    def parseActionRaw(isarString : String) : String = {
    // Here we directly apply transitions to the theory repeatedly
    // to get the (last_observation, action, observation, reward, done) tuple
    var actionTotal : String = ""
    val continue = new Breaks
    // Initialising the state string
    var proof_level_number = getProofLevel
    Breaks.breakable {
      for ((transition, text) <- parse_text(thy1, isarString).force.retrieveNow)
        continue.breakable {
          if (text.trim.isEmpty) continue.break
          actionTotal = actionTotal + ("<\\ISA_STEP>" + text.trim)
        }
    }
    actionTotal
  }

  def parseStateActionWithHammer(isarString: String): String = {
    var stateActionHammerTotal: String = ""
    val continue = new Breaks

    var parse_toplevel: ToplevelState = toplevel
    var stateString = getStateString(parse_toplevel)
    Breaks.breakable {
      for ((transition, text) <- parse_text(thy1, isarString).force.retrieveNow)
        continue.breakable {
          println(stateString)
          println(text)

          // Continue if empty
          if (text.trim.isEmpty) continue.break

          val proof_level = getProofLevel(parse_toplevel)
          // Check if can be solved by hammer
          // hammer_results : (can we try hammer, did hammer work, what is the result if hammer worked)
          val hammer_results: (Boolean, Boolean, String) = {
            if ((proof_level >= 1) && !(stateString contains "No subgoals!") && !(stateString contains "proof (state)") && !(stateString contains "proof (chain)")) {
              val hammered_tuple = {
                try {
                  val raw_hammer_results = prove_with_hammer(parse_toplevel)
                  val hammer_proof = {
                    if (raw_hammer_results._1) {
                      raw_hammer_results._2.head
                    } else " "
                  }
                  (true, raw_hammer_results._1, hammer_proof)
                } catch {
                  case _: TimeoutException => (true, false, " ")
                }
              }

              ("ps -ef" #| "grep z3" #| "awk '{print $2}'" #| "xargs kill -9").!
              ("ps -ef" #| "grep veriT" #| "awk '{print $2}'" #| "xargs kill -9").!
              ("ps -ef" #| "grep cvc4" #| "awk '{print $2}'" #| "xargs kill -9").!
              ("ps -ef" #| "grep eprover" #| "awk '{print $2}'" #| "xargs kill -9").!
              ("ps -ef" #| "grep SPASS" #| "awk '{print $2}'" #| "xargs kill -9").!
              hammered_tuple
            }
            else (false, false, " ")
          }
          stateActionHammerTotal = stateActionHammerTotal + (
            stateString + "<\\STATESEP>" + text.trim + "<\\STATESEP>" + s"$proof_level" + "<\\STATESEP>"
              + s"${hammer_results._1}" + "<\\HAMMERSEP>" + s"${hammer_results._2}"
              + "<\\HAMMERSEP>" + s"${hammer_results._3}" + "<\\TRANSEP>"
            )
          parse_toplevel = singleTransition(transition, parse_toplevel)
          stateString = getStateString(parse_toplevel)
        }
    }
    stateActionHammerTotal
  }

  def parse: String = parseStateAction(fileContent)

  def parse_raw: String = parseActionRaw(fileContent)

  def parse_with_hammer: String = parseStateActionWithHammer(fileContent)


  def step(isar_string: String, top_level_state: ToplevelState, timeout_in_millis: Int = 2000): ToplevelState = {
    // Normal isabelle business
    var tls_to_return: ToplevelState = null
    var stateString: String = ""
    val continue = new Breaks

    val f_st: Future[Unit] = Future.apply {
      Breaks.breakable {
        for ((transition, text) <- parse_text(thy1, isar_string).force.retrieveNow)
          continue.breakable {
            if (text.trim.isEmpty) continue.break
            tls_to_return = singleTransition(transition, top_level_state)
          }
      }
    }
    Await.result(f_st, Duration(timeout_in_millis, "millis"))
    tls_to_return
  }

  def step(isar_string: String): String = {
    // Specific method for extracting data
    if (isar_string == "PISA extract data")
      return parse

    if (isar_string == "PISA extract actions")
      return parse_raw

    // Specific method for extracting data with hammer
    if (isar_string == "PISA extract data with hammer")
      return parse_with_hammer

    // Exit string
    if (isar_string == "exit") {
      isabelle.destroy()
      //      print("Isabelle process destroyed")
      return "Destroyed"
    }
    toplevel = step(isar_string, toplevel)
    getStateString
  }

  // Returns true if the current toplevel state is a proof state & can be proved by Sledgehammer before timeout
//  def check_if_provable_with_Sledgehammer(top_level_state: ToplevelState, timeout_in_millis: Int = 240000): Boolean = {
//    println(check_with_Sledgehammer.getClass.toString)
//    println(top_level_state.getClass.toString)
//    val f_res: Future[Boolean] = Future.apply {
//      check_with_Sledgehammer(top_level_state).force.retrieveNow
//    }
//    Await.result(f_res, Duration(timeout_in_millis, "millis"))
//  }
//
//  def check_if_provable_with_Sledgehammer(): Boolean = {
//    check_if_provable_with_Sledgehammer(toplevel)
//  }

  def prove_with_hammer(top_level_state: ToplevelState, timeout_in_millis: Int = 35000): (Boolean, List[String]) = {
    val f_res: Future[(Boolean, List[String])] = Future.apply {
      prove_with_Sledgehammer(top_level_state).force.retrieveNow
    }
    Await.result(f_res, Duration(timeout_in_millis, "millis"))
  }

  def step_to_transition_text(isar_string: String, after: Boolean = true): String = {
    var stateString: String = ""
    val continue = new Breaks
    Breaks.breakable {
      for ((transition, text) <- parse_text(thy1, fileContent).force.retrieveNow) {
        continue.breakable {
          if (text.trim.isEmpty) continue.break
          val trimmed_text = text.trim.replaceAll("\n", " ").replaceAll(" +", " ")
          if (trimmed_text == isar_string) {
            if (after) stateString = singleTransition(transition)
            return stateString
          }
          stateString = singleTransition(transition)
        }
      }
    }
    println("Did not find the text")
    stateString
  }

  // Manage top level states with the internal map
  def copy_tls: MLValue[ToplevelState] = toplevel.mlValue

  def clone_tls(tls_name: String): Unit = top_level_state_map += (tls_name -> copy_tls)

  def clone_tls(old_name: String, new_name: String): Unit = top_level_state_map += (new_name -> top_level_state_map(old_name))

  def register_tls(name: String, tls: ToplevelState): Unit = top_level_state_map += (name -> tls.mlValue)

  def retrieve_tls(tls_name: String): ToplevelState = ToplevelState.instantiate(top_level_state_map(tls_name))
}