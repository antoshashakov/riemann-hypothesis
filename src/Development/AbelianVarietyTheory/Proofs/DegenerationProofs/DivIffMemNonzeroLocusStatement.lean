module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivIffMemNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.div_iff_mem_nonzeroLocus_and_crd_ratio : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  first | exact @GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus | exact GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus | (intros; apply GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus <;> assumption)
