----------------------------- MODULE ThrottlingSimplified -----------------------------
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS Window, Limit, MaxTime, Clients

(* --algorithm throttling
variables
    Time = 0,
    SimulationTimes = 0..MaxTime,
    Messages = [C \in Clients |-> [T \in SimulationTimes |-> 0]],
    MessagesAttempted = [C \in Clients |-> [T \in SimulationTimes |-> 0]];

define
    GetTimeWindow(T) ==
        {X \in (T-Window)..T : X >= 0 /\ X <= T /\ X >= (T - Window)}
    
        
    Pick(Set) == CHOOSE s \in Set : TRUE

    RECURSIVE SetReduce(_, _, _)
    SetReduce(Op(_, _), set, value) == 
      IF set = {} THEN value
      ELSE 
        LET s == Pick(set)
        IN SetReduce(Op, set \ {s}, Op(s, value)) 
            
    SetSum(set) == 
      LET _op(a, b) == a + b
      IN SetReduce(_op, set, 0)
        
    TotalSentMessages(Sender, TimeWindow) ==
        SetSum({Messages[Sender][T] : T \in TimeWindow})
        
    TotalAttemptedMessages(Sender, TimeWindow) ==
        SetSum({MessagesAttempted[Sender][T] : T \in TimeWindow})
        
end define;   
 
macro SendMessage(Sender)
begin
    Messages[Sender][Time] := Messages[Sender][Time] + 1;
end macro;

macro MarkSendingAttempt(Sender)
begin
    MessagesAttempted[Sender][Time] := MessagesAttempted[Sender][Time] + 1;
end macro;

process Server = 1
begin
    Simulate:
    while Time < MaxTime do
        Time := Time + 1;
    end while;
end process;

process Client \in Clients
begin
    Simulate:
    while Time < MaxTime do
        if TotalSentMessages(self, GetTimeWindow(Time)) < Limit then
            SendMessage(self);
            MarkSendingAttempt(self);
        end if;
    end while;
end process;

    
end algorithm; *)



\* BEGIN TRANSLATION
\* Label Simulate of process Server at line 51 col 5 changed to Simulate_
VARIABLES Time, SimulationTimes, Messages, MessagesAttempted, pc

(* define statement *)
GetTimeWindow(T) ==
    {X \in (T-Window)..T : X >= 0 /\ X <= T /\ X >= (T - Window)}


Pick(Set) == CHOOSE s \in Set : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), set, value) ==
  IF set = {} THEN value
  ELSE
    LET s == Pick(set)
    IN SetReduce(Op, set \ {s}, Op(s, value))

SetSum(set) ==
  LET _op(a, b) == a + b
  IN SetReduce(_op, set, 0)

TotalSentMessages(Sender, TimeWindow) ==
    SetSum({Messages[Sender][T] : T \in TimeWindow})

TotalAttemptedMessages(Sender, TimeWindow) ==
    SetSum({MessagesAttempted[Sender][T] : T \in TimeWindow})


vars == << Time, SimulationTimes, Messages, MessagesAttempted, pc >>

ProcSet == {1} \cup (Clients)

Init == (* Global variables *)
        /\ Time = 0
        /\ SimulationTimes = 0..MaxTime
        /\ Messages = [C \in Clients |-> [T \in SimulationTimes |-> 0]]
        /\ MessagesAttempted = [C \in Clients |-> [T \in SimulationTimes |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Simulate_"
                                        [] self \in Clients -> "Simulate"]

Simulate_ == /\ pc[1] = "Simulate_"
             /\ IF Time < MaxTime
                   THEN /\ Time' = Time + 1
                        /\ pc' = [pc EXCEPT ![1] = "Simulate_"]
                   ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                        /\ Time' = Time
             /\ UNCHANGED << SimulationTimes, Messages, MessagesAttempted >>

Server == Simulate_

Simulate(self) == /\ pc[self] = "Simulate"
                  /\ IF Time < MaxTime
                        THEN /\ IF TotalSentMessages(self, GetTimeWindow(Time)) < Limit
                                   THEN /\ Messages' = [Messages EXCEPT ![self][Time] = Messages[self][Time] + 1]
                                        /\ MessagesAttempted' = [MessagesAttempted EXCEPT ![self][Time] = MessagesAttempted[self][Time] + 1]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << Messages, 
                                                        MessagesAttempted >>
                             /\ pc' = [pc EXCEPT ![self] = "Simulate"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << Messages, MessagesAttempted >>
                  /\ UNCHANGED << Time, SimulationTimes >>

Client(self) == Simulate(self)

Next == Server
           \/ (\E self \in Clients: Client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

FrequencyInvariant ==
    \A C \in Clients: \A T \in SimulationTimes: TotalSentMessages(C, GetTimeWindow(T)) <= Limit
    
PermittedMessagesAcceptedInvariant ==
    \A C \in Clients:
        \A T \in SimulationTimes:
            \/ TotalAttemptedMessages(C, GetTimeWindow(T)) = TotalSentMessages(C, GetTimeWindow(T))
            \/ TotalAttemptedMessages(C, GetTimeWindow(T)) = Limit

=============================================================================
\* Modification History
\* Last modified Tue Dec 19 12:45:24 EET 2017 by flakas
\* Created Wed Nov 08 22:20:23 EET 2017 by flakas
