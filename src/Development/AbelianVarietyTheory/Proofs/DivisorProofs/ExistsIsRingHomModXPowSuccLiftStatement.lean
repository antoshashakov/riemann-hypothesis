module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRingHomModXPowSuccLift
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_isRingHomModXPow_succ_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R), π.FormallySmooth → ∀ n : ℕ, 1 ≤ n → ∀ φ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β n φ → ∃ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_lift_succ | exact GlobalTheory.Nef.PathJet.exists_lift_succ | (intros; apply GlobalTheory.Nef.PathJet.exists_lift_succ <;> assumption)
