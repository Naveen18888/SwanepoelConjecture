module
public import Swanepoel.FiniteFaces
public import Swanepoel.EdgeNeighbourhood
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem crossLinear_ne_zero_of_ne_zero (v : Plane) (hv : v ≠ 0) :
    crossLinear v ≠ 0 := by
  intro he
  have hh := congrArg (fun l : Plane →ₗ[ℝ] ℝ => l (quarterTurn v)) he
  change cross2 v (quarterTurn v)=0 at hh
  rw [cross_quarterTurn] at hh
  exact (norm_ne_zero_iff.mpr hv) (sq_eq_zero_iff.mp hh)

theorem dense_avoiding_parallel_lines {ι : Type*} [Fintype ι]
    (p : ι → Plane) (v : Plane) (hv : v ≠ 0) :
    Dense {z : Plane | ∀ i, cross2 v z ≠ cross2 v (p i)} := by
  have h := dense_finite_intersection
    (fun i => {z : Plane | crossLinear v z ≠ crossLinear v (p i)})
    (fun _ => isOpen_ne.preimage (crossLinear v).continuous_of_finiteDimensional)
    (fun i => dense_complement_affine_line (crossLinear v)
      (crossLinear_ne_zero_of_ne_zero v hv) (crossLinear v (p i)))
  simpa only [Set.iInter_ofPred,crossLinear,LinearMap.coe_mk,AddHom.coe_mk] using h

theorem parallel_line_avoids_points {ι : Type*} (p : ι → Plane) (v z : Plane)
    (hz : ∀ i, cross2 v z ≠ cross2 v (p i)) :
    ∀ i (t : ℝ), z+t • v ≠ p i := by
  intro i t he
  apply hz i
  have hh := congrArg (cross2 v) he
  simpa only [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero] using hh

theorem exists_avoiding_parallel_line_of_isOpen {ι : Type*} [Fintype ι]
    (p : ι → Plane) (v : Plane) (hv : v ≠ 0) (U : Set Plane)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, cross2 v z ≠ cross2 v (p i)) ∧
      ∀ i (t : ℝ), z+t • v ≠ p i := by
  obtain ⟨z,hzU,hz⟩ := (dense_avoiding_parallel_lines p v hv).inter_open_nonempty U hU hne
  exact ⟨z,hzU,hz,parallel_line_avoids_points p v z hz⟩

theorem PennyGraph.exists_vertex_avoiding_parallel_line {n : ℕ} (G : PennyGraph n)
    (v : Plane) (hv : v ≠ 0) (U : Set Plane) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, cross2 v z ≠ cross2 v (G.point i)) ∧
      ∀ i (t : ℝ), z+t • v ≠ G.point i :=
  exists_avoiding_parallel_line_of_isOpen G.point v hv U hU hne

end Swanepoel
