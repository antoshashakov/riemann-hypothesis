module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  first | exact @GlobalTheory.InvDescent.jump_descends | exact GlobalTheory.InvDescent.jump_descends | (intros; apply GlobalTheory.InvDescent.jump_descends <;> assumption)
