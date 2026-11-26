module
public import Swanepoel.TerminalDisplacement
public import Swanepoel.PolygonSeparationAngles
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def cyclicDoubleArea {ι : Type*} [Fintype ι] (next : ι ≃ ι) (p : ι → Plane) : ℝ :=
  ∑ i, cross2 (p i) (p (next i))

def cyclicSignedArea {ι : Type*} [Fintype ι] (next : ι ≃ ι) (p : ι → Plane) : ℝ :=
  cyclicDoubleArea next p/2

def cyclicMidpoint {ι : Type*} (next : ι ≃ ι) (p : ι → Plane) (i : ι) : Plane :=
  (1/2 : ℝ) • (p i+p (next i))

def cyclicEdgeEnergy {ι : Type*} [Fintype ι] (next : ι ≃ ι) (p : ι → Plane) : ℝ :=
  ∑ i, ‖p (next i)-p i‖^2

def centeredVertexEnergy {ι : Type*} [Fintype ι] (p : ι → Plane) (c : Plane) : ℝ :=
  ∑ i, ‖p i-c‖^2

def cross2RightLinear (u : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun v := cross2 u v
  map_add' x y := cross2_add_right u x y
  map_smul' a x := by simp only [cross2_smul_right,RingHom.id_apply,smul_eq_mul]

theorem cyclic_edge_sum_zero {ι : Type*} [Fintype ι] (next : ι ≃ ι) (p : ι → Plane) :
    (∑ i, (p (next i)-p i))=0 := by
  rw [Finset.sum_sub_distrib,next.sum_comp,sub_self]

theorem cross2_translate (x y c : Plane) :
    cross2 (x+c) (y+c)=cross2 x y+cross2 c (y-x) := by
  simp [cross2]
  ring

theorem cyclicDoubleArea_translate {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) :
    cyclicDoubleArea next (fun i => p i+c)=cyclicDoubleArea next p := by
  have hz : (∑ i, cross2 c (p (next i)-p i))=0 := by
    change (∑ i, cross2RightLinear c (p (next i)-p i))=0
    rw [← map_sum,cyclic_edge_sum_zero,map_zero]
  simp only [cyclicDoubleArea,cross2_translate,Finset.sum_add_distrib,hz,add_zero]

theorem cyclicDoubleArea_sub {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) :
    cyclicDoubleArea next (fun i => p i-c)=cyclicDoubleArea next p := by
  simpa only [sub_eq_add_neg] using cyclicDoubleArea_translate next p (-c)

theorem midpoint_cross_edge (x y c : Plane) :
    cross2 ((1/2 : ℝ) • (x+y)-c) (y-x)=cross2 (x-c) (y-c) := by
  simp [cross2]
  ring

theorem cyclicDoubleArea_eq_midpoint_edges {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) :
    cyclicDoubleArea next p=
      ∑ i, cross2 (cyclicMidpoint next p i-c) (p (next i)-p i) := by
  rw [← cyclicDoubleArea_sub next p c]
  unfold cyclicDoubleArea
  apply Finset.sum_congr rfl
  intro i _
  exact (midpoint_cross_edge (p i) (p (next i)) c).symm

theorem midpoint_norm_sq_identity (x y c : Plane) :
    4*‖(1/2 : ℝ) • (x+y)-c‖^2+‖y-x‖^2=
      2*(‖x-c‖^2+‖y-c‖^2) := by
  have hm : (1/2 : ℝ) • (x+y)-c=(1/2 : ℝ) • ((x-c)+(y-c)) := by module
  have hd : y-x=(y-c)-(x-c) := by abel
  rw [hm,hd,norm_smul,Real.norm_eq_abs]
  norm_num
  have ha := norm_add_sq_real (x-c) (y-c)
  have hs := norm_sub_sq_real (y-c) (x-c)
  have hi : inner ℝ (y-c) (x-c)=inner ℝ (x-c) (y-c) := real_inner_comm _ _
  rw [hi,← hd] at hs
  nlinarith

theorem cyclic_midpoint_energy_identity {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) :
    4*centeredVertexEnergy (cyclicMidpoint next p) c+cyclicEdgeEnergy next p=
      4*centeredVertexEnergy p c := by
  have hp : (∑ i, ‖p (next i)-c‖^2)=∑ i, ‖p i-c‖^2 :=
    next.sum_comp (fun i => ‖p i-c‖^2)
  calc
    _ = ∑ i, (4*‖cyclicMidpoint next p i-c‖^2+‖p (next i)-p i‖^2) := by
      simp only [centeredVertexEnergy,cyclicEdgeEnergy,Finset.sum_add_distrib,Finset.mul_sum]
    _ = ∑ i, 2*(‖p i-c‖^2+‖p (next i)-c‖^2) :=
      Finset.sum_congr rfl (fun i _ => midpoint_norm_sq_identity _ _ _)
    _ = 4*centeredVertexEnergy p c := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,hp]
      unfold centeredVertexEnergy
      ring

theorem planeComplex_norm (x : Plane) : ‖planeComplex x‖=‖x‖ := by
  have hs : ‖planeComplex x‖^2=‖x‖^2 := by
    rw [Complex.sq_norm,EuclideanSpace.real_norm_sq_eq]
    simp [planeComplex,Complex.normSq_apply,Fin.sum_univ_two]
    ring
  nlinarith [norm_nonneg (planeComplex x),norm_nonneg x]

theorem cross2_eq_complex_im (x y : Plane) :
    cross2 x y=(star (planeComplex x)*planeComplex y).im := by
  simp [planeComplex,cross2,Complex.mul_im]
  ring

theorem cross2_abs_le_norm_mul (x y : Plane) : |cross2 x y|≤‖x‖*‖y‖ := by
  have he : cross2 x y=inner ℝ (quarterTurn x) y := by
    simp [cross2,quarterTurn,PiLp.inner_apply,Fin.sum_univ_two]
    ring
  rw [he]
  simpa only [quarterTurn_norm] using abs_real_inner_le_norm (quarterTurn x) y

theorem cyclic_area_cauchy {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) :
    (cyclicDoubleArea next p)^2≤
      centeredVertexEnergy (cyclicMidpoint next p) c*cyclicEdgeEnergy next p := by
  let M (i : ι) := ‖cyclicMidpoint next p i-c‖
  let E (i : ι) := ‖p (next i)-p i‖
  have ha : |cyclicDoubleArea next p|≤∑ i, M i*E i := by
    rw [cyclicDoubleArea_eq_midpoint_edges next p c]
    calc
      _≤∑ i, |cross2 (cyclicMidpoint next p i-c) (p (next i)-p i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _≤∑ i, M i*E i := Finset.sum_le_sum (fun i _ => cross2_abs_le_norm_mul _ _)
  have hnonneg : 0≤∑ i, M i*E i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ M E
  have hs : (cyclicDoubleArea next p)^2≤(∑ i, M i*E i)^2 := by
    nlinarith [abs_nonneg (cyclicDoubleArea next p),sq_abs (cyclicDoubleArea next p)]
  exact hs.trans hcs

theorem cyclic_area_from_vertex_energy {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) (c : Plane) (L : ℝ)
    (hV : centeredVertexEnergy p c≤L*cyclicEdgeEnergy next p) :
    4*(cyclicDoubleArea next p)^2≤(4*L-1)*(cyclicEdgeEnergy next p)^2 := by
  have hid := cyclic_midpoint_energy_identity next p c
  have hc := cyclic_area_cauchy next p c
  have hE : 0≤cyclicEdgeEnergy next p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 4*centeredVertexEnergy (cyclicMidpoint next p) c≤
      (4*L-1)*cyclicEdgeEnergy next p := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hm hE
  nlinarith

theorem cyclicDoubleArea_eq_complex_sum_im {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) :
    cyclicDoubleArea next p=
      (∑ i, star (planeComplex (p i))*planeComplex (p (next i))).im := by
  simp only [cyclicDoubleArea,Complex.im_sum,← cross2_eq_complex_im]

theorem cyclicEdgeEnergy_eq_complex {ι : Type*} [Fintype ι]
    (next : ι ≃ ι) (p : ι → Plane) :
    cyclicEdgeEnergy next p=∑ i, ‖planeComplex (p (next i))-planeComplex (p i)‖^2 := by
  simp only [← map_sub,planeComplex_norm,cyclicEdgeEnergy]

end Swanepoel
