---- MODULE MC ----
EXTENDS ThrottlingSimplified, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
C1, C2
----

\* MV CONSTANT definitions Clients
const_154651889957425000 == 
{C1, C2}
----

\* SYMMETRY definition
symm_154651889957426000 == 
Permutations(const_154651889957425000)
----

\* CONSTANT definitions @modelParameterConstants:0Window
const_154651889957427000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2MaxTime
const_154651889957428000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3Limit
const_154651889957429000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154651889957430000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154651889957431000 ==
FrequencyInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154651889957432000 ==
PermittedMessagesAcceptedInvariant
----
=============================================================================
\* Modification History
\* Created Thu Jan 03 14:34:59 EET 2019 by flakas
