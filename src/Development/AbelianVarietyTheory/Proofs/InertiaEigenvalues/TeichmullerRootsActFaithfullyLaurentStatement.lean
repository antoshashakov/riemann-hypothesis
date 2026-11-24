module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootsActFaithfullyLaurent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.teichmuller_roots_act_faithfully_laurent : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩), (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧ Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c := by
  first | exact @GlobalTheory.DeltaInv.main | exact GlobalTheory.DeltaInv.main | (intros; apply GlobalTheory.DeltaInv.main <;> assumption)
