module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NaturalDegreeZeroHomologyIso
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.natural_degree_zero_homology_iso : ∀ {R : Type} [CommRing R] {𝒜 : Type 1} [Category.{0} 𝒜] [HasZeroMorphisms 𝒜]
    (T₁ T₂ : 𝒜 ⥤ CochainComplex (ModuleCat.{0} R) ℕ) [T₁.PreservesZeroMorphisms] [T₂.PreservesZeroMorphisms]
    (ε : ∀ G, (T₁.obj G).X 0 ≅ (T₂.obj G).X 0),
    (∀ {G G' : 𝒜} (φ : G ⟶ G'), (T₁.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ (T₂.map φ).f 0) →
    (∀ (G : 𝒜) (x : (T₁.obj G).X 0),
      ((T₁.obj G).d 0 1).hom x = 0 ↔ ((T₂.obj G).d 0 1).hom ((ε G).hom.hom x) = 0) →
    (∀ G : 𝒜, ∃ (I Q : 𝒜) (i : G ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      ((ShortComplex.mk i p w).map T₁).ShortExact ∧ ((ShortComplex.mk i p w).map T₂).ShortExact ∧
      ∀ n, IsZero ((T₁.obj I).homology (n + 1)) ∧ IsZero ((T₂.obj I).homology (n + 1))) →
    ∀ (n : ℕ) (G : 𝒜), Nonempty ((T₁.obj G).homology n ≅ (T₂.obj G).homology n) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.DimShift.homology_nonempty_iso | exact GlobalTheory.CompanionTheory.Hodge.DimShift.homology_nonempty_iso | (intros; apply GlobalTheory.CompanionTheory.Hodge.DimShift.homology_nonempty_iso <;> assumption)
