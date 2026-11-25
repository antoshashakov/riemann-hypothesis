module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegree
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.first_inequality_sUnits_prime_degree : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  first | exact @GlobalTheory.CNorm.first_inequality_sUnits_prime | exact GlobalTheory.CNorm.first_inequality_sUnits_prime | (intros; apply GlobalTheory.CNorm.first_inequality_sUnits_prime <;> assumption)
