module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)), (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧ (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧ ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  first | exact @GlobalTheory.Decompl.FixL.fixSub_ladic | exact GlobalTheory.Decompl.FixL.fixSub_ladic | (intros; apply GlobalTheory.Decompl.FixL.fixSub_ladic <;> assumption)
