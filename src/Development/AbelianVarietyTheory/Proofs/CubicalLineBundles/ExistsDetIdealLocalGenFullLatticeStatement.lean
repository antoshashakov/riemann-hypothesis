module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDetIdealLocalGenFullLattice
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_detIdeal_localGen_full_lattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K), (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) → (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) → IsLocGen p M.det I := by
  first | exact @GlobalTheory.LamF.exists_detIdeal_isLocGen | exact GlobalTheory.LamF.exists_detIdeal_isLocGen | (intros; apply GlobalTheory.LamF.exists_detIdeal_isLocGen <;> assumption)
