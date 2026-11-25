module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContraIsSubquotient
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isSubquotient_contra_of_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W), IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | exact GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient <;> assumption)
