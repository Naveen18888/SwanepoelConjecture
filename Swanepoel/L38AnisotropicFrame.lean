module
public import Swanepoel.L38AnisotropicWalk
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def l38AxisFrame (u : Plane) : Plane→ₗ[ℝ]Plane where
  toFun p := cartPoint (inner ℝ u p) (cross2 u p)
  map_add' p q := by
    ext i
    fin_cases i <;> simp [cartPoint,inner_add_right,cross2_add_right]
  map_smul' r p := by
    ext i
    fin_cases i <;> simp [cartPoint,real_inner_smul_right,cross2_smul_right]

theorem l38AxisFrame_norm (u : Plane) (hu : ‖u‖=1) (p : Plane) :
    ‖l38AxisFrame u p‖=‖p‖ := by
  have hc := cross2_sq_add_inner_sq u p
  rw [hu] at hc
  have hn := l38_cartPoint_norm_sq (inner ℝ u p) (cross2 u p)
  change ‖cartPoint (inner ℝ u p) (cross2 u p)‖=‖p‖
  nlinarith only [hc,hn,norm_nonneg (cartPoint (inner ℝ u p) (cross2 u p)),norm_nonneg p]

theorem l38AxisFrame_cross (u : Plane) (hu : ‖u‖=1) (p q : Plane) :
    cross2 (l38AxisFrame u p) (l38AxisFrame u q)=cross2 p q := by
  have hucoords : (u 0)^2+(u 1)^2=1 := by
    have hh := EuclideanSpace.real_norm_sq_eq u
    rw [hu] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  calc
    _ = ((u 0)^2+(u 1)^2)*cross2 p q := by
      simp [l38AxisFrame,cartPoint,cross2,PiLp.inner_apply,Fin.sum_univ_two]
      ring
    _ = cross2 p q := by rw [hucoords,one_mul]

theorem l38AxisFrame_rightNormal (u p : Plane) :
    rightNormalMap (l38AxisFrame u p)=l38AxisFrame u (rightNormalMap p) := by
  ext i
  fin_cases i <;>
    simp [l38AxisFrame,cartPoint,rightNormalMap,quarterTurn,cross2,PiLp.inner_apply,Fin.sum_univ_two] <;>
    ring

theorem l38AxisFrame_area {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (p : ι→Plane) (u : Plane) (hu : ‖u‖=1) :
    cyclicSignedArea next (fun i => l38AxisFrame u (p i))=cyclicSignedArea next p := by
  unfold cyclicSignedArea cyclicDoubleArea
  simp_rw [l38AxisFrame_cross u hu]

theorem l38_oriented_bank_walk_area_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (next : Equiv.Perm ι) (hcycle : next.IsCycleOn Set.univ) (p : ι→Plane)
    (u : Plane) (hu : ‖u‖=1) (bank : ι→Prop) (l : ι→ℝ) (d : ι→Plane)
    (hl : ∀ i,0≤l i) (hd : ∀ i,‖d i‖=1)
    (hedge : ∀ i,p (next i)-p i=l i • d i)
    (hbank : ∀ i,bank i→Real.sqrt 3/2 ≤ inner ℝ u (rightNormalMap (d i))) :
    4*l38CertificateArea*cyclicSignedArea next p≤
      (∑ i,if bank i then l i/3 else l i)^2 := by
  have hd' (i : ι) : ‖l38AxisFrame u (d i)‖=1 := (l38AxisFrame_norm u hu _).trans (hd i)
  have hedge' (i : ι) : l38AxisFrame u (p (next i))-l38AxisFrame u (p i)=
      l i • l38AxisFrame u (d i) := by
    rw [← map_sub,hedge i,map_smul]
  have hbank' (i : ι) (hb : bank i) :
      rightNormalMap (l38AxisFrame u (d i))∈l38BankArc l38SupportAxis := by
    constructor
    · rw [rightNormalMap_norm,hd' i]
    · rw [l38AxisFrame_rightNormal]
      simpa [l38SupportAxis,l38AxisFrame,cartPoint,PiLp.inner_apply,Fin.sum_univ_two]
        using hbank i hb
  have hcal := l38_bank_walk_area_bound next hcycle (fun i => l38AxisFrame u (p i))
    bank l (fun i => l38AxisFrame u (d i)) hl hd' hedge' hbank'
  rw [l38AxisFrame_area next p u hu] at hcal
  exact hcal

end Swanepoel
