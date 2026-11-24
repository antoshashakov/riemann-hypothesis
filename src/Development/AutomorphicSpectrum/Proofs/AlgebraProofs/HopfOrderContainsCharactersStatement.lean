module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

theorem _root_.GlobalTheory.T.hopf_order_contains_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder <;> assumption)
