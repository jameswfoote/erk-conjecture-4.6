import Bistability
import Source

/-! These ascriptions and commands audit the mathematical statements independently
of their proof scripts. Type synonyms have the dimensions in the published model. -/
example : ERK.Target.Conjecture46 := ERK.conjecture_4_6
#print ERK.Target.PositiveClassSink
#print ERK.Singular.Hurwitz
#check @ERK.Singular.eventually_hurwitz
#print axioms ERK.Singular.eventually_hurwitz
#check @ERK.Lift.stable_branch
#print axioms ERK.Lift.stable_branch
#check @ERK.Lift.schur_on_graph
#print axioms ERK.Lift.schur_on_graph
#check ERK.Scalar.two_scalar_sinks
#print axioms ERK.Scalar.two_scalar_sinks
#check @ERK.First.fast_hurwitz
#print axioms ERK.First.fast_hurwitz
#check @ERK.First.two_sinks
#print axioms ERK.First.two_sinks
#check ERK.Fast.enzyme_det
#print axioms ERK.Fast.enzyme_det
#check @ERK.Second.graph_fast_stable
#print axioms ERK.Second.graph_fast_stable
#check @ERK.Second.eta_sink_branch
#print axioms ERK.Second.eta_sink_branch
#check @ERK.common_enzyme_parameter
#print axioms ERK.common_enzyme_parameter
#check @ERK.Model.eta_conjugacy
#print axioms ERK.Model.eta_conjugacy
#check ERK.Source.reaction_model_eq_equation4
#print axioms ERK.Source.reaction_model_eq_equation4
#check ERK.Source.same_class_iff
#print axioms ERK.Source.same_class_iff
#check ERK.Source.class_dimension
#print axioms ERK.Source.class_dimension
#check ERK.conjecture_4_6
#print axioms ERK.conjecture_4_6
