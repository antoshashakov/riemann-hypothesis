module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInjectiveRingHomIsLocalHomAndExtend
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first | exact @GlobalTheory.finite_injective_localHom_and_extend | exact GlobalTheory.finite_injective_localHom_and_extend | (intros; apply GlobalTheory.finite_injective_localHom_and_extend <;> assumption)
