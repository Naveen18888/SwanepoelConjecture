module
public import Swanepoel.Drawing
public import Mathlib.Tactic.FinCases
@[expose] public section

noncomputable section
namespace Swanepoel

theorem cross2_add_left (x y e : Plane) : cross2 (x+y) e=cross2 x e+cross2 y e := by
  simp [cross2]
  ring

theorem cross2_smul_left (x e : Plane) (a : ℝ) : cross2 (a • x) e=a*cross2 x e := by
  simp [cross2]
  ring

theorem cross2_self (x : Plane) : cross2 x x=0 := by unfold cross2; ring

theorem cramer_reconstruct (u v w : Plane) (hn : cross2 u v≠0) :
    (cross2 w v/cross2 u v) • u+(cross2 u w/cross2 u v) • v=w := by
  have hid : cross2 w v • u+cross2 u w • v=cross2 u v • w := by
    ext i
    fin_cases i <;> simp [cross2] <;> ring
  calc
    _ = (cross2 u v)⁻¹ • (cross2 w v • u+cross2 u w • v) := by
      simp only [div_eq_mul_inv]
      module
    _ = (cross2 u v)⁻¹ • (cross2 u v • w) := by rw [hid]
    _ = w := by rw [smul_smul,inv_mul_cancel₀ hn,one_smul]

namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

theorem cross_ne_zero (ht : G.TriangleFree) : cross2 C.u C.v≠0 := by
  intro h
  have ha := C.area_lower ht
  rw [h,abs_zero] at ha
  have hs := Real.sqrt_nonneg (3 : ℝ)
  linarith

def cellPoint (r s : ℝ) : Plane := G.point C.a+r • C.u+s • C.v
def coordU (z : Plane) : ℝ := cross2 (z-G.point C.a) C.v/cross2 C.u C.v
def coordV (z : Plane) : ℝ := cross2 C.u (z-G.point C.a)/cross2 C.u C.v

theorem coordU_cellPoint (ht : G.TriangleFree) (r s : ℝ) :
    C.coordU (C.cellPoint r s)=r := by
  have he : C.cellPoint r s-G.point C.a=r • C.u+s • C.v := by dsimp [cellPoint]; abel
  rw [coordU,he,cross2_add_left,cross2_smul_left,cross2_smul_left,cross2_self]
  field_simp [C.cross_ne_zero ht]
  ring

theorem coordV_cellPoint (ht : G.TriangleFree) (r s : ℝ) :
    C.coordV (C.cellPoint r s)=s := by
  have he : C.cellPoint r s-G.point C.a=r • C.u+s • C.v := by dsimp [cellPoint]; abel
  rw [coordV,he,cross2_add_right,cross2_smul_right,cross2_smul_right,cross2_self]
  field_simp [C.cross_ne_zero ht]
  ring

theorem reconstruct (ht : G.TriangleFree) (z : Plane) :
    C.cellPoint (C.coordU z) (C.coordV z)=z := by
  have h := cramer_reconstruct C.u C.v (z-G.point C.a) (C.cross_ne_zero ht)
  dsimp [cellPoint,coordU,coordV]
  rw [add_assoc,h]
  abel

def openRegion : Set Plane := {z | 0<C.coordU z ∧ C.coordU z<1 ∧ 0<C.coordV z ∧ C.coordV z<1}
def closedRegion : Set Plane := {z | 0≤C.coordU z ∧ C.coordU z≤1 ∧ 0≤C.coordV z ∧ C.coordV z≤1}
def boundary : Set Plane := G.edgeTrace C.a C.b ∪ G.edgeTrace C.b C.c ∪
  G.edgeTrace C.c C.d ∪ G.edgeTrace C.d C.a

theorem continuous_coordU : Continuous C.coordU := by
  have h0 : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  unfold coordU cross2
  exact (((h0.sub continuous_const).mul continuous_const).sub
    ((h1.sub continuous_const).mul continuous_const)).div_const _

theorem continuous_coordV : Continuous C.coordV := by
  have h0 : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  unfold coordV cross2
  exact ((continuous_const.mul (h1.sub continuous_const)).sub
    (continuous_const.mul (h0.sub continuous_const))).div_const _

theorem isOpen_openRegion : IsOpen C.openRegion :=
  (isOpen_lt continuous_const C.continuous_coordU).inter
    ((isOpen_lt C.continuous_coordU continuous_const).inter
      ((isOpen_lt continuous_const C.continuous_coordV).inter
        (isOpen_lt C.continuous_coordV continuous_const)))

theorem isClosed_closedRegion : IsClosed C.closedRegion :=
  (isClosed_le continuous_const C.continuous_coordU).inter
    ((isClosed_le C.continuous_coordU continuous_const).inter
      ((isClosed_le continuous_const C.continuous_coordV).inter
        (isClosed_le C.continuous_coordV continuous_const)))

theorem openRegion_subset_closedRegion : C.openRegion⊆C.closedRegion := by
  rintro z ⟨hr0,hr1,hs0,hs1⟩
  exact ⟨hr0.le,hr1.le,hs0.le,hs1.le⟩

theorem closure_openRegion_subset : closure C.openRegion⊆C.closedRegion :=
  closure_minimal C.openRegion_subset_closedRegion C.isClosed_closedRegion

theorem cellPoint_mem_openRegion (ht : G.TriangleFree) {r s : ℝ}
    (hr0 : 0<r) (hr1 : r<1) (hs0 : 0<s) (hs1 : s<1) : C.cellPoint r s∈C.openRegion := by
  exact ⟨by rwa [C.coordU_cellPoint ht],by rwa [C.coordU_cellPoint ht],
    by rwa [C.coordV_cellPoint ht],by rwa [C.coordV_cellPoint ht]⟩

theorem continuous_cellPoint : Continuous (fun p : ℝ × ℝ => C.cellPoint p.1 p.2) :=
  (continuous_const.add (continuous_fst.smul continuous_const)).add
    (continuous_snd.smul continuous_const)

theorem isPreconnected_openRegion (ht : G.TriangleFree) : IsPreconnected C.openRegion := by
  have he : C.openRegion=(fun p : ℝ × ℝ => C.cellPoint p.1 p.2) ''
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨hr0,hr1,hs0,hs1⟩
      exact ⟨(C.coordU z,C.coordV z),⟨⟨hr0,hr1⟩,hs0,hs1⟩,C.reconstruct ht z⟩
    · rintro ⟨⟨r,s⟩,⟨⟨hr0,hr1⟩,hs0,hs1⟩,rfl⟩
      exact C.cellPoint_mem_openRegion ht hr0 hr1 hs0 hs1
  rw [he]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ C.continuous_cellPoint.continuousOn

end RhombusCell
end Swanepoel
