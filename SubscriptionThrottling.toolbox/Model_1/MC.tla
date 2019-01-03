---- MODULE MC ----
EXTENDS SubscriptionThrottling, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
FirstSite, SecondSite, ThirdSite
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
FirstEmail
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
FirstIP
----

\* MV CONSTANT definitions SITES
const_1546438989935358000 == 
{FirstSite, SecondSite, ThirdSite}
----

\* MV CONSTANT definitions EMAIL_ADDRESSES
const_1546438989935359000 == 
{FirstEmail}
----

\* MV CONSTANT definitions IPS
const_1546438989935360000 == 
{FirstIP}
----

\* SYMMETRY definition
symm_1546438989935361000 == 
Permutations(const_1546438989935358000) \union Permutations(const_1546438989935359000) \union Permutations(const_1546438989935360000)
----

\* CONSTANT definitions @modelParameterConstants:2TIME_LIMIT
const_1546438989935362000 == 
20
----

\* CONSTANT definitions @modelParameterConstants:4EMAILS_RECEIVED_ATTACK_THRESHOLD
const_1546438989935363000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:5TIME_THROTTLE_WINDOW_SIZE
const_1546438989935364000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6TIME_THROTTLE_LIMIT
const_1546438989935365000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:7MAX_EMAIL_ADDRESS_SUBSCRIPTIONS
const_1546438989935366000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546438989935367000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546438989935368000 ==
MaxEmailsReceivedInvariant
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 16:23:09 EET 2019 by flakas
