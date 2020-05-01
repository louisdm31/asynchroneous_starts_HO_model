theory HOModel
imports Main
begin

declare if_split_asm [split] \<comment> \<open>perform default perform case splitting on conditionals\<close>

section \<open>Heard-Of Algorithms\<close>

subsection \<open>The Consensus Problem\<close>

text \<open>
  We are interested in the verification of fault-tolerant distributed algorithms.
  The Consensus problem is paradigmatic in this area. Stated
  informally, it assumes that all processes participating in the algorithm
  initially propose some value, and that they may at some point decide some value.
  It is required that every process eventually decides, and that all processes
  must decide the same value.

  More formally, we represent runs of algorithms as \<open>\<omega>\<close>-sequences of
  configurations (vectors of process states). Hence, a run is modeled as
  a function of type \<open>nat \<Rightarrow> 'proc \<Rightarrow> 'pst\<close> where type variables 
  \<open>'proc\<close> and \<open>'pst\<close> represent types of processes and process
  states, respectively. The Consensus property is expressed with respect
  to a collection \<open>vals\<close> of initially proposed values (one per process) 
  and an observer function \<open>dec::'pst \<Rightarrow> val option\<close> that retrieves the decision
  (if any) from a process state. The Consensus problem is stated as the conjunction
  of the following properties:
  \begin{description}
  \item[Integrity.] Processes can only decide initially proposed values.
  \item[Agreement.] Whenever processes \<open>p\<close> and \<open>q\<close> decide,
    their decision values must be the same. (In particular, process \<open>p\<close>
    may never change the value it decides, which is referred to as Irrevocability.)
  \item[Termination.] Every process decides eventually.
  \end{description}

  The above properties are sometimes only required of non-faulty processes, since
  nothing can be required of a faulty process.
  The Heard-Of model does not attribute faults to processes, and therefore the
  above formulation is appropriate in this framework.
\<close>



type_synonym
  ('proc,'pst) run = "nat \<Rightarrow> 'proc \<Rightarrow> 'pst"

definition
  consensus :: "('proc \<Rightarrow> 'val) \<Rightarrow> ('pst \<Rightarrow> 'val option) \<Rightarrow> ('proc,'pst) run \<Rightarrow> bool"
where
  "consensus vals dec rho \<equiv>
     (\<forall>n p v. dec (rho n p) = Some v \<longrightarrow> v \<in> range vals)
   \<and> (\<forall>m n p q v w. dec (rho m p) = Some v \<and> dec (rho n q) = Some w 
         \<longrightarrow> v = w)
   \<and> (\<forall>p. \<exists>n. dec (rho n p) \<noteq> None)"

text \<open>
  A variant of the Consensus problem replaces the Integrity requirement by
  \begin{description}
  \item[Validity.] If all processes initially propose the same value \<open>v\<close>
    then every process may only decide \<open>v\<close>.
  \end{description}
\<close>

definition weak_consensus where
  "weak_consensus vals dec rho \<equiv>
     (\<forall>v. (\<forall>p. vals p = v) \<longrightarrow> (\<forall>n p w. dec (rho n p) = Some w \<longrightarrow> w = v))
   \<and> (\<forall>m n p q v w. dec (rho m p) = Some v \<and> dec (rho n q) = Some w 
         \<longrightarrow> v = w)
   \<and> (\<forall>p. \<exists>n. dec (rho n p) \<noteq> None)"

text \<open>
  Clearly, \<open>consensus\<close> implies \<open>weak_consensus\<close>.
\<close>

lemma consensus_then_weak_consensus:
  assumes "consensus vals dec rho"
  shows "weak_consensus vals dec rho"
  using assms by (auto simp: consensus_def weak_consensus_def image_def)

text \<open>
  Over Boolean values (``binary Consensus''), \<open>weak_consensus\<close>
  implies \<open>consensus\<close>, hence the two problems are equivalent.
  In fact, this theorem holds more generally whenever at most two
  different values are proposed initially (i.e., \<open>card (range vals) \<le> 2\<close>).
\<close>

lemma binary_weak_consensus_then_consensus:
  assumes bc: "weak_consensus (vals::'proc \<Rightarrow> bool) dec rho"
  shows "consensus vals dec rho"
proof -
  { \<comment> \<open>Show the Integrity property, the other conjuncts are the same.\<close>
    fix n p v
    assume dec: "dec (rho n p) = Some v"
    have "v \<in> range vals"
    proof (cases "\<exists>w. \<forall>p. vals p = w")
      case True
      then obtain w where w: "\<forall>p. vals p = w" ..
      with bc have "dec (rho n p) \<in> {Some w, None}" by (auto simp: weak_consensus_def)
      with dec w show ?thesis by (auto simp: image_def)
    next
      case False
      \<comment> \<open>In this case both possible values occur in @{text "vals"}, and the result is trivial.\<close>
      thus ?thesis by (auto simp: image_def)
    qed
  } note integrity = this
  from bc show ?thesis
    unfolding consensus_def weak_consensus_def by (auto elim!: integrity)
qed

text \<open>
  The algorithms that we are going to verify solve the Consensus or weak Consensus
  problem, under different hypotheses about the kinds and number of faults.
\<close>


subsection \<open>A Generic Representation of Heard-Of Algorithms\<close>

text \<open>
  Charron-Bost and Schiper~\cite{charron:heardof} introduce
  the Heard-Of (HO) model for representing fault-tolerant
  distributed algorithms. In this model, algorithms execute in communication-closed
  rounds: at any round~$r$, processes only receive messages that were sent for
  that round. For every process~$p$ and round~$r$, the ``heard-of set'' $HO(p,r)$
  denotes the set of processes from which~$p$ receives a message in round~$r$.
  Since every process is assumed to send a message to all processes in each round,
  the complement of $HO(p,r)$ represents the set of faults that may affect~$p$ in
  round~$r$ (messages that were not received, e.g. because the sender crashed,
  because of a network problem etc.).

  The HO model expresses hypotheses on the faults tolerated by an algorithm
  through ``communication predicates'' that constrain the sets $HO(p,r)$
  that may occur during an execution. Charron-Bost and Schiper show that
  standard fault models can be represented in this form.

  The original HO model is sufficient for representing algorithms
  tolerating benign failures such as process crashes or message loss. A later
  extension for algorithms tolerating Byzantine (or value) failures~\cite{biely:tolerating} 
  adds a second collection of sets $SHO(p,r) \subseteq HO(p,r)$ that contain those
  processes $q$ from which process $p$ receives the message that $q$ was indeed
  supposed to send for round $r$ according to the algorithm. In other words, 
  messages from processes in $HO(p,r) \setminus SHO(p,r)$ were corrupted, be it
  due to errors during message transmission or because of the sender was faulty or
  lied deliberately. For both benign and Byzantine errors, the HO model registers
  the fault but does not try to identify the faulty component (i.e., designate the
  sending or receiving process, or the communication channel as the ``culprit'').

  Executions of HO algorithms are defined with respect to collections
  $HO(p,r)$ and $SHO(p,r)$. However, the code of a process does not have
  access to these sets. In particular, process $p$ has no way of determining
  if a message it received from another process $q$ corresponds to what $q$
  should have sent or if it has been corrupted.

  Certain algorithms rely on the assignment of ``coordinator'' processes for
  each round. Just as the collections $HO(p,r)$, the definitions assume an
  external coordinator assignment such that $coord(p,r)$ denotes the coordinator
  of process $p$ and round $r$. Again, the correctness of algorithms may depend
  on hypotheses about coordinator assignments -- e.g., it may be assumed that
  processes agree sufficiently often on who the current coordinator is.

  The following definitions provide a generic representation of HO and SHO algorithms
  in Isabelle/HOL. A (coordinated) HO algorithm is described by the following parameters:
  \begin{itemize}
  \item a finite type \<open>'proc\<close> of processes,
  \item a type \<open>'pst\<close> of local process states,
  \item a type \<open>'msg\<close> of messages sent in the course of the algorithm,
  \item a predicate \<open>CinitState\<close> such that \<open>CinitState p st crd\<close> is
    true precisely of the initial states \<open>st\<close> of process \<open>p\<close>, assuming
    that \<open>crd\<close> is the initial coordinator of \<open>p\<close>,
  \item a function \<open>sendMsg\<close> where \<open>sendMsg r p q st\<close> yields
    the message that process \<open>p\<close> sends to process \<open>q\<close> at round
    \<open>r\<close>, given its local state \<open>st\<close>, and
  \item a predicate \<open>CnextState\<close> where \<open>CnextState r p st msgs crd st'\<close>
    characterizes the successor states \<open>st'\<close> of process \<open>p\<close> at round
    \<open>r\<close>, given current state \<open>st\<close>, the vector
    \<open>msgs :: 'proc \<Rightarrow> 'msg option\<close> of messages that \<open>p\<close> received at
    round \<open>r\<close> (\<open>msgs q = None\<close> indicates that no message has been
    received from process \<open>q\<close>),
    and process \<open>crd\<close> as the coordinator for the following round.
  \end{itemize}
  Note that every process can store the coordinator for the current round in its
  local state, and it is therefore not necessary to make the coordinator a parameter
  of the message sending function \<open>sendMsg\<close>.

  We represent an algorithm by a record as follows.
\<close>

datatype 'msg message = Content "'msg" | Bot | Void
datatype 'pst proc_state = Active "'pst" | Aslept

record ('proc, 'pst, 'msg) CHOAlgorithm =
  CinitState ::  "'proc \<Rightarrow> 'pst \<Rightarrow> 'proc \<Rightarrow> bool"
  sendMsg ::   "'proc \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> 'msg"
  CnextState :: "'proc \<Rightarrow> 'pst \<Rightarrow> ('proc \<Rightarrow> 'msg message) \<Rightarrow> 'proc \<Rightarrow> 'pst \<Rightarrow> bool"

text \<open>
  For non-coordinated HO algorithms, the coordinator argument of functions
  \<open>CinitState\<close> and \<open>CnextState\<close> is irrelevant, and we
  define utility functions that omit that argument.
\<close>

definition isNCAlgorithm where
  "isNCAlgorithm alg \<equiv> 
      (\<forall>p st crd crd'. CinitState alg p st crd = CinitState alg p st crd')
   \<and> (\<forall>p st msgs crd crd' st'. CnextState alg p st msgs crd st'
                               = CnextState alg p st msgs crd' st')"

definition initState where
  "initState alg p st \<equiv> CinitState alg p st undefined"

definition nextState where
  "nextState alg p st msgs st' \<equiv> CnextState alg p st msgs undefined st'"

text \<open>
  A \emph{heard-of assignment} associates a set of processes with each
  process. The following type is used to represent the collections $HO(p,r)$
  and $SHO(p,r)$ for fixed round $r$.
%
  Similarly, a \emph{coordinator assignment} associates a process (its coordinator)
  to each process.
\<close>

type_synonym
  'proc HO = "'proc \<Rightarrow> 'proc set"

type_synonym
  'proc coord = "'proc \<Rightarrow> 'proc"

text \<open>
  An execution of an HO algorithm is defined with respect to HO and SHO
  assignments that indicate, for every round \<open>r\<close> and every process \<open>p\<close>,
  from which sender processes \<open>p\<close> receives messages (resp., uncorrupted
  messages) at round \<open>r\<close>.

%% That's the intention, but we don't enforce this in the definitions.
%  Obviously, SHO sets are always included in HO sets, for the same process and round.

  The following definitions formalize this idea. We define ``coarse-grained''
  executions whose unit of atomicity is the round of execution. At each round,
  the entire collection of processes performs a transition according to the
  \<open>CnextState\<close> function of the algorithm. Consequently, a system state is
  simply described by a configuration, i.e. a function assigning a process state
  to every process. This definition of executions may appear surprising for an
  asynchronous distributed system, but it simplifies system verification,
  compared to a ``fine-grained'' execution model that records individual events
  such as message sending and reception or local transitions. We will justify
  later why the ``coarse-grained'' model is sufficient for verifying interesting
  correctness properties of HO algorithms.

  The predicate \<open>CSHOinitConfig\<close> describes the possible initial configurations
  for algorithm \<open>A\<close> (remember that a configuration is a function that assigns
  local states to every process).
\<close>

text \<open>
  Given the current configuration \<open>cfg\<close> and the HO and SHO sets \<open>HOp\<close>
  and \<open>SHOp\<close> for process \<open>p\<close> at round \<open>r\<close>, the function
  \<open>SHOmsgVectors\<close> computes the set of possible vectors of messages that
  process \<open>p\<close> may receive. For processes \<open>q \<notin> HOp\<close>, \<open>p\<close> 
  receives no message (represented as value \<open>None\<close>). For processes
  \<open>q \<in> SHOp\<close>, \<open>p\<close> receives the message that \<open>q\<close> computed
  according to the \<open>sendMsg\<close> function of the algorithm. For the remaining
  processes \<open>q \<in> HOp - SHOp\<close>, \<open>p\<close> may receive some arbitrary value.
\<close>

text \<open>
  Predicate \<open>CSHOnextConfig\<close> uses the preceding function and the algorithm's
  \<open>CnextState\<close> function to characterize the possible successor configurations
  in a coarse-grained step, and predicate \<open>CSHORun\<close> defines (coarse-grained)
  executions \<open>rho\<close> of an HO algorithm.
\<close>

fun HOrcvMsgs_q :: "'proc \<Rightarrow> ('proc, 'pst, 'msg) CHOAlgorithm  \<Rightarrow> 'proc \<Rightarrow>
                         'pst proc_state \<Rightarrow> 'msg message" where
 "HOrcvMsgs_q q A p (Active s) = Content (sendMsg A q p s)" |
 "HOrcvMsgs_q q A p Aslept = Bot"

definition HOrcvdMsgs :: "('proc, 'pst, 'a) CHOAlgorithm \<Rightarrow> 'proc \<Rightarrow>
                          'proc set \<Rightarrow> ('proc \<Rightarrow> 'pst proc_state)
                          \<Rightarrow> 'proc \<Rightarrow> 'a message" where
  "HOrcvdMsgs A p HO cfg \<equiv>
   \<lambda>q. if q \<in> HO then HOrcvMsgs_q q A p (cfg q) else Void"

definition CHOnextConfig where
  "CHOnextConfig A cfg HO coord cfg' \<equiv>
   \<forall>p s.       cfg  p = Active s \<longrightarrow>
         (\<exists>s'. cfg' p = Active s' \<and> CnextState A p s (HOrcvdMsgs A p (HO p) cfg) (coord p) s')"

definition CHOinitConfig where
  "CHOinitConfig A rho coord \<equiv>
  \<forall>p (n::nat) s. (n > 0 \<longrightarrow> rho (n-1) p = Aslept) \<longrightarrow> rho n p = Active s \<longrightarrow> CinitState A p s (coord n p)"

definition getInitValue :: "(nat \<Rightarrow> 'proc \<Rightarrow> 'pst proc_state) \<Rightarrow> 'proc \<Rightarrow> 'pst proc_state" where
  "getInitValue rho p \<equiv> if \<forall>n. rho n p = Aslept then Aslept else
    rho (Max ({n + 1 | n. rho n p = Aslept } \<union> {0})) p"


definition CHORun where
  "CHORun A rho HOs coords \<equiv> CHOinitConfig A rho coords
   \<and> (\<forall>r. CHOnextConfig A (rho r) (HOs r) (coords (Suc r))
                             (rho (Suc r)))"

lemma nonAsleepAgain : assumes "rho n p \<noteq> Aslept" and "CHORun A rho HO coord"
  shows "rho ((m::nat)+n) p \<noteq> Aslept"
proof (induction m)
  case 0
  show "rho (0+n) p \<noteq> Aslept" using assms by auto
next
  case (Suc x)
  assume "rho (x+n) p \<noteq> Aslept"
  hence "\<exists>s. rho (x + n) p = Active s" by (cases "rho (x+n) p") auto
  hence "\<exists>s. rho (Suc x + n) p = Active s"
    using assms CHORun_def CHORun_def CHOnextConfig_def by (metis add.commute add_Suc_right)
  then show ?case by (cases "rho (Suc x + n) p") auto
qed

text \<open>
  For non-coordinated algorithms. the \<open>coord\<close> arguments of the above functions
  are irrelevant. We define similar functions that omit that argument, and relate
  them to the above utility functions for these algorithms.
\<close>
definition HOinitConfig where
  "HOinitConfig A cfg \<equiv> CHOinitConfig A cfg (\<lambda>n. \<lambda>q. undefined)"

lemma HOinitConfig_eq:
  "HOinitConfig A rho = (\<forall>p (n::nat) s. (n > 0 \<longrightarrow> rho (n-1) p = Aslept) \<longrightarrow>
                                        rho n p = Active s \<longrightarrow> initState A p s)"
  by (auto simp: HOinitConfig_def CHOinitConfig_def initState_def)

definition HOnextConfig where
  "HOnextConfig A cfg HO cfg' \<equiv>
   CHOnextConfig A cfg HO (\<lambda>q. undefined) cfg'"

definition HORun :: "('proc, 'pst, 'msg) CHOAlgorithm \<Rightarrow>
                      (nat \<Rightarrow> 'proc \<Rightarrow> 'pst proc_state) \<Rightarrow> (nat \<Rightarrow> 'proc \<Rightarrow> 'proc set) \<Rightarrow> bool" where
  "HORun A rho HOs \<equiv>
   CHORun A rho HOs (\<lambda>r q. undefined)"

lemma HORun_eq:
  "HORun A rho HOs =
     (HOinitConfig A rho
   \<and> (\<forall>r. HOnextConfig A (rho r) (HOs r) (rho (Suc r))))"
  by (auto simp: HORun_def CHORun_def HOinitConfig_def HOnextConfig_def)

(*
text \<open>
  The following derived proof rules are immediate consequences of
  the definition of \<open>CHORun\<close>; they simplify automatic reasoning.
\<close>

lemma CHORun_0:
  assumes "CHORun A rho HOs coords" 
      and "\<And>cfg. CHOinitConfig A cfg (coords 0) \<Longrightarrow> P cfg"
  shows "P (rho 0)"
using assms unfolding CHORun_eq by blast

lemma CHORun_Suc:
  assumes "CHORun A rho HOs coords"
  and "\<And>r. CHOnextConfig A r (rho r) (HOs r) (coords (Suc r)) (rho (Suc r))
            \<Longrightarrow> P r"
  shows "P n"
using assms unfolding CHORun_eq by blast

lemma CHORun_induct:
  assumes run: "CHORun A rho HOs coords"
  and init: "CHOinitConfig A (rho 0) (coords 0) \<Longrightarrow> P 0"
  and step: "\<And>r. \<lbrakk> P r; CHOnextConfig A r (rho r) (HOs r) (coords (Suc r)) 
                                      (rho (Suc r)) \<rbrakk> \<Longrightarrow> P (Suc r)"
  shows "P n"
using run unfolding CHORun_eq by (induct n, auto elim: init step)
*)

text \<open>
  Because algorithms will not operate for arbitrary HO, SHO, and coordinator
  assignments, these are constrained by a \emph{communication predicate}.
  For convenience, we split this predicate into a \emph{per Round} part that
  is expected to hold at every round and a \emph{global} part that must hold
  of the sequence of (S)HO assignments and may thus express liveness assumptions.

  In the parlance of~\cite{charron:heardof}, a \emph{HO machine} is an HO algorithm
  augmented with a communication predicate. We therefore define (C)(S)HO machines as
  the corresponding extensions of the record defining an HO algorithm.
\<close>

record ('proc, 'pst, 'msg) HOMachine = "('proc, 'pst, 'msg) CHOAlgorithm" +
  HOcommPerRd::"'proc HO \<Rightarrow> bool"
  HOcommGlobal::"(nat \<Rightarrow> 'proc HO) \<Rightarrow> bool"

record ('proc, 'pst, 'msg) CHOMachine = "('proc, 'pst, 'msg) CHOAlgorithm" +
  CHOcommPerRd::"nat \<Rightarrow> 'proc HO \<Rightarrow> 'proc coord \<Rightarrow> bool"
  CHOcommGlobal::"(nat \<Rightarrow> 'proc HO) \<Rightarrow> (nat \<Rightarrow> 'proc coord) \<Rightarrow> bool"


end \<comment> \<open>theory HOModel\<close>
