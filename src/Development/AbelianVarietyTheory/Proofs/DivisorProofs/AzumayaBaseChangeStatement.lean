module

public import Mathlib.Algebra.Azumaya.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped TensorProduct
open Function

theorem _root_.GlobalTheory.T.azumaya_base_change : ∀ (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ], IsAzumaya S (S ⊗[A] Λ) := by
  first | (exact @GlobalTheory.isAzumaya_baseChange) | (exact GlobalTheory.isAzumaya_baseChange) | (intros; apply GlobalTheory.isAzumaya_baseChange <;> assumption)
