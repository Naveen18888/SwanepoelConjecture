module
public import Swanepoel.PentagonRemovalAccounting
public import Swanepoel.PentagonSpokes
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.FamilyAreaComparison {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : Prop :=
  ∃ A : ℝ, Real.sqrt 3/2*(G.familyR ht Y : ℝ)≤A ∧
    A≤(G.familyBoundaryEndCount Y : ℝ)^2/(4*Real.pi)

theorem PennyGraph.familyR_nonneg {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : 0≤G.familyR ht Y := by
  unfold PennyGraph.familyR
  positivity

theorem PennyGraph.small_boundary_family_quadratic {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hsmall : 5*(G.familyBoundaryEndCount Y : ℤ)≤8*G.familyK Y)
    (harea : G.FamilyAreaComparison ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 := by
  obtain ⟨A,hlower,hupper⟩ := harea
  exact small_boundary_quadratic_bound_int (G.familyK Y) (G.familyBoundaryEndCount Y)
    (G.familyR ht Y) A (G.family_K_nonneg ht hY) (Nat.cast_nonneg _)
    (G.familyR_nonneg ht Y) hsmall hlower hupper

theorem PennyGraph.family_quadratic_of_area_and_pentagons {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (harea : ∀ (Y : Finset (PlaneFace G)), G.IsJoinClosed ht Y →
      5*(G.familyBoundaryEndCount Y : ℤ)≤8*G.familyK Y → G.FamilyAreaComparison ht Y)
    (hpentagon : G.PentagonCrossingEstimate ht)
    (Y : Finset (PlaneFace G)) (hY : G.IsJoinClosed ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 := by
  have hAll : ∀ m : ℕ, ∀ Z : Finset (PlaneFace G), Z.card=m → G.IsJoinClosed ht Z →
      10000*G.familyR ht Z≤2379*(G.familyK Z)^2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Z hcard hZ
      by_cases hsmall : 5*(G.familyBoundaryEndCount Z : ℤ)≤8*G.familyK Z
      · exact G.small_boundary_family_quadratic ht hZ hsmall (harea Z hZ hsmall)
      · have hlarge : 8*G.familyK Z<5*(G.familyBoundaryEndCount Z : ℤ) := by omega
        obtain ⟨F,hF,hfive,hports⟩ := G.large_boundary_exists_five_port_boundary_face ht hZ hlarge
        have C := G.five_port_removal_counts ht hZ F hF hfive hports
        have hless : (Z\{F}).card<m := by have := C.defects; omega
        have hrec := ih (Z\{F}).card hless (Z\{F}) rfl C.remainder_closed
        have hKR : G.familyK (Z\{F})=G.familyK Z-3 := by have := C.K; omega
        rw [hKR] at hrec
        have hdisjoint := G.five_port_internal_crossings_zero ht F (hZ.subset_defects hF) hdegree hfive
        have hmixed := hpentagon Z hZ F hF hfive hports
        exact pentagon_quadratic_step (G.familyK Z) (G.familyBoundaryEndCount Z)
          (G.familyR ht Z) (G.familyR ht (Z\{F})) (G.family_K_nonneg ht hZ) hlarge
          (C.loss_bound hdisjoint hmixed) hrec
  exact hAll Y.card Y rfl hY

end Swanepoel
