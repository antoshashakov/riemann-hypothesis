module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.exists_continuous_coords_unramified_frobenius : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  first | exact @GlobalTheory.PMon.coef_unr_continuous | exact GlobalTheory.PMon.coef_unr_continuous | (intros; apply GlobalTheory.PMon.coef_unr_continuous <;> assumption)
