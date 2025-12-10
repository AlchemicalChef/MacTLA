import Foundation

enum TLATemplates {
    static let basicSpecification = """
    ---- MODULE Spec ----
    EXTENDS Naturals, Sequences

    VARIABLES state

    Init == state = 0

    Next == state' = state + 1

    Spec == Init /\\ [][Next]_state

    ====
    """

    static let twoPhaseCommit = """
    ---- MODULE TwoPhaseCommit ----
    EXTENDS Naturals, FiniteSets

    CONSTANT RM  \\* Set of resource managers

    VARIABLES
        rmState,      \\* rmState[r] is the state of resource manager r
        tmState,      \\* State of the transaction manager
        tmPrepared,   \\* Set of RMs from which TM has received "Prepared"
        msgs          \\* Set of messages sent

    Message == [type: {"Prepared", "Commit", "Abort"}] \\cup
               [type: {"Prepared"}, rm: RM]

    TPTypeOK ==
        /\\ rmState \\in [RM -> {"working", "prepared", "committed", "aborted"}]
        /\\ tmState \\in {"init", "committed", "aborted"}
        /\\ tmPrepared \\subseteq RM
        /\\ msgs \\subseteq Message

    Init ==
        /\\ rmState = [r \\in RM |-> "working"]
        /\\ tmState = "init"
        /\\ tmPrepared = {}
        /\\ msgs = {}

    TMRcvPrepared(r) ==
        /\\ tmState = "init"
        /\\ [type |-> "Prepared", rm |-> r] \\in msgs
        /\\ tmPrepared' = tmPrepared \\cup {r}
        /\\ UNCHANGED <<rmState, tmState, msgs>>

    TMCommit ==
        /\\ tmState = "init"
        /\\ tmPrepared = RM
        /\\ tmState' = "committed"
        /\\ msgs' = msgs \\cup {[type |-> "Commit"]}
        /\\ UNCHANGED <<rmState, tmPrepared>>

    TMAbort ==
        /\\ tmState = "init"
        /\\ tmState' = "aborted"
        /\\ msgs' = msgs \\cup {[type |-> "Abort"]}
        /\\ UNCHANGED <<rmState, tmPrepared>>

    RMPrepare(r) ==
        /\\ rmState[r] = "working"
        /\\ rmState' = [rmState EXCEPT ![r] = "prepared"]
        /\\ msgs' = msgs \\cup {[type |-> "Prepared", rm |-> r]}
        /\\ UNCHANGED <<tmState, tmPrepared>>

    RMChooseToAbort(r) ==
        /\\ rmState[r] = "working"
        /\\ rmState' = [rmState EXCEPT ![r] = "aborted"]
        /\\ UNCHANGED <<tmState, tmPrepared, msgs>>

    RMRcvCommitMsg(r) ==
        /\\ [type |-> "Commit"] \\in msgs
        /\\ rmState' = [rmState EXCEPT ![r] = "committed"]
        /\\ UNCHANGED <<tmState, tmPrepared, msgs>>

    RMRcvAbortMsg(r) ==
        /\\ [type |-> "Abort"] \\in msgs
        /\\ rmState' = [rmState EXCEPT ![r] = "aborted"]
        /\\ UNCHANGED <<tmState, tmPrepared, msgs>>

    Next ==
        \\/ TMCommit
        \\/ TMAbort
        \\/ \\E r \\in RM:
              TMRcvPrepared(r) \\/ RMPrepare(r) \\/ RMChooseToAbort(r)
                \\/ RMRcvCommitMsg(r) \\/ RMRcvAbortMsg(r)

    Spec == Init /\\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>

    Consistent ==
        \\A r1, r2 \\in RM: ~(rmState[r1] = "committed" /\\ rmState[r2] = "aborted")

    ====
    """

    static let modelConfig = """
    SPECIFICATION Spec

    CONSTANT RM = {r1, r2, r3}

    INVARIANT TPTypeOK
    INVARIANT Consistent
    """

    static let plusCalAlgorithm = """
    ---- MODULE Algorithm ----
    EXTENDS Naturals, TLC

    (*--algorithm Example
    variables x = 0, y = 0;

    process Producer = 1
    begin
      Produce:
        x := x + 1;
        goto Produce;
    end process;

    process Consumer = 2
    begin
      Consume:
        await x > 0;
        y := y + 1;
        x := x - 1;
        goto Consume;
    end process;

    end algorithm; *)

    ====
    """

    static let mutexExample = """
    ---- MODULE Mutex ----
    EXTENDS Naturals

    CONSTANT N  \\* Number of processes

    VARIABLES pc, turn, flag

    vars == <<pc, turn, flag>>

    ProcSet == 1..N

    Init ==
        /\\ pc = [i \\in ProcSet |-> "ncs"]
        /\\ turn = 1
        /\\ flag = [i \\in ProcSet |-> FALSE]

    ncs(self) ==
        /\\ pc[self] = "ncs"
        /\\ pc' = [pc EXCEPT ![self] = "try"]
        /\\ UNCHANGED <<turn, flag>>

    try(self) ==
        /\\ pc[self] = "try"
        /\\ flag' = [flag EXCEPT ![self] = TRUE]
        /\\ pc' = [pc EXCEPT ![self] = "wait"]
        /\\ UNCHANGED turn

    wait(self) ==
        /\\ pc[self] = "wait"
        /\\ \\/ turn = self
           \\/ ~flag[turn]
        /\\ pc' = [pc EXCEPT ![self] = "cs"]
        /\\ UNCHANGED <<turn, flag>>

    cs(self) ==
        /\\ pc[self] = "cs"
        /\\ pc' = [pc EXCEPT ![self] = "exit"]
        /\\ UNCHANGED <<turn, flag>>

    exit(self) ==
        /\\ pc[self] = "exit"
        /\\ turn' = (self %% N) + 1
        /\\ flag' = [flag EXCEPT ![self] = FALSE]
        /\\ pc' = [pc EXCEPT ![self] = "ncs"]

    Next == \\E self \\in ProcSet:
        \\/ ncs(self)
        \\/ try(self)
        \\/ wait(self)
        \\/ cs(self)
        \\/ exit(self)

    Spec == Init /\\ [][Next]_vars

    MutualExclusion ==
        \\A i, j \\in ProcSet: (i /= j) => ~(pc[i] = "cs" /\\ pc[j] = "cs")

    ====
    """

    static let plusCalMutex = """
    ---- MODULE PlusCalMutex ----
    EXTENDS Naturals, TLC

    (*--fair algorithm Mutex
    variables flag = [i \\in {0, 1} |-> FALSE], turn = 0;

    process Thread \\in {0, 1}
    variables other = 0;
    begin
      Start:
        other := 1 - self;
      Lock:
        flag[self] := TRUE;
      Wait:
        await ~flag[other] \\/ turn = self;
      CS:
        skip; \\* Critical section
      Unlock:
        flag[self] := FALSE;
        turn := other;
        goto Lock;
    end process;

    end algorithm; *)

    ====
    """

    static let raftConsensus = """
    ---- MODULE Raft ----
    \\* Simplified Raft consensus algorithm
    EXTENDS Naturals, FiniteSets, Sequences

    CONSTANT Server     \\* Set of servers
    CONSTANT Value      \\* Set of values that can be proposed

    VARIABLES
        currentTerm,    \\* currentTerm[s] is the current term of server s
        state,          \\* state[s] is the state of server s (Follower, Candidate, Leader)
        votedFor,       \\* votedFor[s] is the candidate that s voted for in current term
        log,            \\* log[s] is the log of server s
        commitIndex,    \\* commitIndex[s] is the highest committed entry index
        votesGranted,   \\* votesGranted[s] is the set of servers that voted for s
        msgs            \\* Set of messages in the network

    vars == <<currentTerm, state, votedFor, log, commitIndex, votesGranted, msgs>>

    \\* Server states
    Follower  == "Follower"
    Candidate == "Candidate"
    Leader    == "Leader"

    \\* Message types
    RequestVote     == "RequestVote"
    RequestVoteResp == "RequestVoteResp"
    AppendEntries   == "AppendEntries"
    AppendEntriesResp == "AppendEntriesResp"

    \\* Type invariant
    TypeOK ==
        /\\ currentTerm \\in [Server -> Nat]
        /\\ state \\in [Server -> {Follower, Candidate, Leader}]
        /\\ votedFor \\in [Server -> Server \\cup {None}]
        /\\ log \\in [Server -> Seq([term: Nat, value: Value])]
        /\\ commitIndex \\in [Server -> Nat]
        /\\ votesGranted \\in [Server -> SUBSET Server]

    \\* Initialize all servers as followers
    Init ==
        /\\ currentTerm = [s \\in Server |-> 0]
        /\\ state = [s \\in Server |-> Follower]
        /\\ votedFor = [s \\in Server |-> None]
        /\\ log = [s \\in Server |-> <<>>]
        /\\ commitIndex = [s \\in Server |-> 0]
        /\\ votesGranted = [s \\in Server |-> {}]
        /\\ msgs = {}

    \\* Server s times out and starts an election
    Timeout(s) ==
        /\\ state[s] \\in {Follower, Candidate}
        /\\ state' = [state EXCEPT ![s] = Candidate]
        /\\ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
        /\\ votedFor' = [votedFor EXCEPT ![s] = s]
        /\\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
        /\\ msgs' = msgs \\cup {[type |-> RequestVote,
                                  term |-> currentTerm[s] + 1,
                                  src  |-> s,
                                  dst  |-> t] : t \\in Server \\ {s}}
        /\\ UNCHANGED <<log, commitIndex>>

    \\* Server s receives a RequestVote and grants or denies it
    HandleRequestVote(s, m) ==
        LET grant == /\\ m.term >= currentTerm[s]
                     /\\ (votedFor[s] = None \\/ votedFor[s] = m.src)
        IN
        /\\ m.type = RequestVote
        /\\ m.dst = s
        /\\ IF grant
           THEN /\\ votedFor' = [votedFor EXCEPT ![s] = m.src]
                /\\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                /\\ msgs' = msgs \\cup {[type |-> RequestVoteResp,
                                          term |-> m.term,
                                          src  |-> s,
                                          dst  |-> m.src,
                                          granted |-> TRUE]}
           ELSE /\\ msgs' = msgs \\cup {[type |-> RequestVoteResp,
                                          term |-> currentTerm[s],
                                          src  |-> s,
                                          dst  |-> m.src,
                                          granted |-> FALSE]}
                /\\ UNCHANGED <<currentTerm, votedFor>>
        /\\ UNCHANGED <<state, log, commitIndex, votesGranted>>

    \\* Server s receives a vote response
    HandleVoteResponse(s, m) ==
        /\\ m.type = RequestVoteResp
        /\\ m.dst = s
        /\\ m.term = currentTerm[s]
        /\\ state[s] = Candidate
        /\\ m.granted
        /\\ votesGranted' = [votesGranted EXCEPT ![s] = @ \\cup {m.src}]
        /\\ msgs' = msgs \\ {m}
        /\\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex>>

    \\* Candidate s becomes leader when it has majority
    BecomeLeader(s) ==
        /\\ state[s] = Candidate
        /\\ Cardinality(votesGranted[s]) * 2 > Cardinality(Server)
        /\\ state' = [state EXCEPT ![s] = Leader]
        /\\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted, msgs>>

    \\* Leader s appends a new entry to the log
    ClientRequest(s, v) ==
        /\\ state[s] = Leader
        /\\ log' = [log EXCEPT ![s] = Append(@, [term |-> currentTerm[s], value |-> v])]
        /\\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, votesGranted, msgs>>

    Next ==
        \\/ \\E s \\in Server: Timeout(s)
        \\/ \\E s \\in Server: BecomeLeader(s)
        \\/ \\E s \\in Server, v \\in Value: ClientRequest(s, v)
        \\/ \\E s \\in Server, m \\in msgs:
              HandleRequestVote(s, m) \\/ HandleVoteResponse(s, m)

    Spec == Init /\\ [][Next]_vars

    \\* Safety: At most one leader per term
    ElectionSafety ==
        \\A s1, s2 \\in Server:
            (state[s1] = Leader /\\ state[s2] = Leader /\\ currentTerm[s1] = currentTerm[s2])
            => s1 = s2

    \\* Placeholder constant for None (no vote)
    None == CHOOSE x: x \\notin Server

    ====
    """
}
