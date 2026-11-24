module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeaklySmall
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.weakly_small_of_not_isUnit_of_dvd_pow : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U := by
  first | exact @GlobalTheory.WeakClosed.weakly_small | exact GlobalTheory.WeakClosed.weakly_small | (intros; apply GlobalTheory.WeakClosed.weakly_small <;> assumption)
