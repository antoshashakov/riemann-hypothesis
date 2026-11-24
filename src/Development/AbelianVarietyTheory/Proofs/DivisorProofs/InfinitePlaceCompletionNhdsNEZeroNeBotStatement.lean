module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
