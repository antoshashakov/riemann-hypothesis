module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
public import Development.EtaleCohomology.DivisorCycles.FinEmbedPf
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace LateralTheory.Fin.FinEmbed
theorem etale_semisimple_finite_embedding_holds_assembled : LateralTheory.DivDb.FinEmbed := by
  apply LateralTheory.DivDb.FinEmbedPf.FinEmbed_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinEmbed := etale_semisimple_finite_embedding_holds_assembled
end LateralTheory.Fin.FinEmbed
