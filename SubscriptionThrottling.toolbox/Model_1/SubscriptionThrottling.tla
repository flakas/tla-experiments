----------------------- MODULE SubscriptionThrottling -----------------------
\* Simulation
\* Time = 0..20
\* Sites = ["blog1", "BLOG2", "blog3"]
\* IPs = ["1.1.1.1", "1.1.1.2", "1.1.1.3", "1.1.1.4", "1.1.1.5"]
\* EmailAddresses = ["1@example.org", "2@example.org", "3@example.org", "4@example.org", "5@example.org", "6@example.org", "7@example.org"]
\* AttackedAddresses = ["1@example.org"]

\* Throttling algo config
\* IPBasedLimit = 2
\* IPBasedExponent = 2
\* EmailBasedLimit = 2
\* EmailBasedExponent

\* Targets
\* NumberOfEmailsReceivedByAddress = 5

EXTENDS Integers, TLC
CONSTANTS TIME_LIMIT, SITES, IPS, EMAIL_ADDRESSES
CONSTANTS EMAILS_RECEIVED_ATTACK_THRESHOLD
CONSTANTS TIME_THROTTLE_WINDOW_SIZE, TIME_THROTTLE_LIMIT
CONSTANTS MAX_EMAIL_ADDRESS_SUBSCRIPTIONS

(* --algorithm SubscriptionThrottling

variables 
    Time = 0,
    SimulationTimes = 0..TIME_LIMIT,
    TotalEmailsReceived = [Address \in EMAIL_ADDRESSES |-> 0],
    SiteIPSubscriptions = [Site \in SITES |-> [IP \in IPS |-> [T \in SimulationTimes |-> 0]]],
    SiteEmailSubscriptions = [Site \in SITES |-> [Email \in EMAIL_ADDRESSES |-> 0]];
    
define
    GetTimeWindow(T, WindowSize) ==
        {X \in (T-WindowSize)..T : X >= 0 /\ X <= T /\ X >= (T - WindowSize)}
    
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
        
    TotalPerformedIPSubscriptions(Site, IP, TimeWindow) ==
        SetSum({SiteIPSubscriptions[Site][IP][T] : T \in TimeWindow})
    
end define;   


macro Subscribe(IP, Site, EmailAddress) 
begin
    if TotalPerformedIPSubscriptions(Site, IP, GetTimeWindow(Time, TIME_THROTTLE_WINDOW_SIZE)) < TIME_THROTTLE_LIMIT
            /\ SiteEmailSubscriptions[Site][EmailAddress] < MAX_EMAIL_ADDRESS_SUBSCRIPTIONS then
        TotalEmailsReceived[EmailAddress] := TotalEmailsReceived[EmailAddress] + 1;
        SiteIPSubscriptions[Site][IP][Time] := SiteIPSubscriptions[Site][IP][Time] + 1;
        SiteEmailSubscriptions[Site][EmailAddress] := SiteEmailSubscriptions[Site][EmailAddress] + 1;
    end if;
end macro;

process GlobalTimeTracker = -1
begin
    AdvanceTime:
        while Time < TIME_LIMIT do
            Time := Time + 1;
        end while;
end process;

process Spammer \in IPS
begin
    AttemptSubscription:
        while Time < TIME_LIMIT do
            with Site \in SITES; EmailAddress \in EMAIL_ADDRESSES do
                Subscribe(self, Site, EmailAddress)
            end with;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES Time, SimulationTimes, TotalEmailsReceived, SiteIPSubscriptions, 
          SiteEmailSubscriptions, pc

(* define statement *)
GetTimeWindow(T, WindowSize) ==
    {X \in (T-WindowSize)..T : X >= 0 /\ X <= T /\ X >= (T - WindowSize)}

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

TotalPerformedIPSubscriptions(Site, IP, TimeWindow) ==
    SetSum({SiteIPSubscriptions[Site][IP][T] : T \in TimeWindow})


vars == << Time, SimulationTimes, TotalEmailsReceived, SiteIPSubscriptions, 
           SiteEmailSubscriptions, pc >>

ProcSet == {-1} \cup (IPS)

Init == (* Global variables *)
        /\ Time = 0
        /\ SimulationTimes = 0..TIME_LIMIT
        /\ TotalEmailsReceived = [Address \in EMAIL_ADDRESSES |-> 0]
        /\ SiteIPSubscriptions = [Site \in SITES |-> [IP \in IPS |-> [T \in SimulationTimes |-> 0]]]
        /\ SiteEmailSubscriptions = [Site \in SITES |-> [Email \in EMAIL_ADDRESSES |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self = -1 -> "AdvanceTime"
                                        [] self \in IPS -> "AttemptSubscription"]

AdvanceTime == /\ pc[-1] = "AdvanceTime"
               /\ IF Time < TIME_LIMIT
                     THEN /\ Time' = Time + 1
                          /\ pc' = [pc EXCEPT ![-1] = "AdvanceTime"]
                     ELSE /\ pc' = [pc EXCEPT ![-1] = "Done"]
                          /\ Time' = Time
               /\ UNCHANGED << SimulationTimes, TotalEmailsReceived, 
                               SiteIPSubscriptions, SiteEmailSubscriptions >>

GlobalTimeTracker == AdvanceTime

AttemptSubscription(self) == /\ pc[self] = "AttemptSubscription"
                             /\ IF Time < TIME_LIMIT
                                   THEN /\ \E Site \in SITES:
                                             \E EmailAddress \in EMAIL_ADDRESSES:
                                               IF TotalPerformedIPSubscriptions(Site, self, GetTimeWindow(Time, TIME_THROTTLE_WINDOW_SIZE)) < TIME_THROTTLE_LIMIT
                                                       /\ SiteEmailSubscriptions[Site][EmailAddress] < MAX_EMAIL_ADDRESS_SUBSCRIPTIONS
                                                  THEN /\ TotalEmailsReceived' = [TotalEmailsReceived EXCEPT ![EmailAddress] = TotalEmailsReceived[EmailAddress] + 1]
                                                       /\ SiteIPSubscriptions' = [SiteIPSubscriptions EXCEPT ![Site][self][Time] = SiteIPSubscriptions[Site][self][Time] + 1]
                                                       /\ SiteEmailSubscriptions' = [SiteEmailSubscriptions EXCEPT ![Site][EmailAddress] = SiteEmailSubscriptions[Site][EmailAddress] + 1]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << TotalEmailsReceived, 
                                                                       SiteIPSubscriptions, 
                                                                       SiteEmailSubscriptions >>
                                        /\ pc' = [pc EXCEPT ![self] = "AttemptSubscription"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                        /\ UNCHANGED << TotalEmailsReceived, 
                                                        SiteIPSubscriptions, 
                                                        SiteEmailSubscriptions >>
                             /\ UNCHANGED << Time, SimulationTimes >>

Spammer(self) == AttemptSubscription(self)

Next == GlobalTimeTracker
           \/ (\E self \in IPS: Spammer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MaxEmailsReceivedInvariant ==
    \A Address \in EMAIL_ADDRESSES:
        TotalEmailsReceived[Address] < EMAILS_RECEIVED_ATTACK_THRESHOLD

=============================================================================
\* Modification History
\* Last modified Tue Jan 01 21:00:02 EET 2019 by flakas
\* Created Fri Dec 28 13:26:52 EET 2018 by flakas
