---- MODULE MC ----
EXTENDS SubscriptionThrottling, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
S1, S2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
E1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
IP1
----

\* MV CONSTANT definitions SITES
const_154669202185714000 == 
{S1, S2}
----

\* MV CONSTANT definitions EMAIL_ADDRESSES
const_154669202185715000 == 
{E1}
----

\* MV CONSTANT definitions IPS
const_154669202185716000 == 
{IP1}
----

\* SYMMETRY definition
symm_154669202185717000 == 
Permutations(const_154669202185714000) \union Permutations(const_154669202185715000) \union Permutations(const_154669202185716000)
----

\* CONSTANT definitions @modelParameterConstants:2TIME_LIMIT
const_154669202185718000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:3TIME_THROTTLE_LIMIT
const_154669202185719000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4EMAILS_RECEIVED_ATTACK_THRESHOLD
const_154669202185720000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:5TIME_THROTTLE_WINDOW_SIZE
const_154669202185721000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:7MAX_EMAIL_ADDRESS_SUBSCRIPTIONS
const_154669202185722000 == 
5
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154669202185723000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154669202185724000 ==
MaxTotalEmailsReceivedByAddressInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154669202185725000 ==
AbleToSubscribeAtLeastOnceInvariant
----
=============================================================================
\* Modification History
\* Created Sat Jan 05 14:40:21 EET 2019 by flakas
