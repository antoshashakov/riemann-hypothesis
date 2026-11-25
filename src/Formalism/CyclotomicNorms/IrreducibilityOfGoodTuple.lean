module

public import Formalism.CyclotomicNorms.StatementT
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.Jordan
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.RestrictionOfBlocksAndJordan
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.CyclotomicNorms

theorem restriction : Restriction := restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity

theorem irreducibility_of_good_tuple : IrreducibilityCriterion := irreducibility_of_restriction restriction

end Formalism.CyclotomicNorms
