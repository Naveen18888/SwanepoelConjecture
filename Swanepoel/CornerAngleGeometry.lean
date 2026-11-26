module
public import Swanepoel.FullCornerSectors
public import Swanepoel.UnitCirclePhases
public import Swanepoel.UnitCapGeometry
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem unitAngleVector_add_three (ρ : ℝ) :
    unitAngleVector (ρ+3)= -unitAngleVector ρ := by
  ext i
  fin_cases i <;> simp [unitAngleVector,
    show Real.pi/3*(ρ+3)=Real.pi/3*ρ+Real.pi by ring,
    Real.cos_add_pi,Real.sin_add_pi]

theorem unitAngleVector_add_eq_of_eq {a b : ℝ}
    (h : unitAngleVector a=unitAngleVector b) (t : ℝ) :
    unitAngleVector (a+t)=unitAngleVector (b+t) := by
  have hc := congrArg (fun z : Plane => z 0) h
  have hs := congrArg (fun z : Plane => z 1) h
  change Real.cos (Real.pi/3*a)=Real.cos (Real.pi/3*b) at hc
  change Real.sin (Real.pi/3*a)=Real.sin (Real.pi/3*b) at hs
  ext i
  fin_cases i <;> simp [unitAngleVector,mul_add,Real.cos_add,Real.sin_add,hc,hs]

theorem unit_corner_gap_bounds (ρ g : ℝ) (hg0 : 0≤g) (hg6 : g<6)
    (hinner : inner ℝ (unitAngleVector ρ) (unitAngleVector (ρ-g))<1/2) :
    1<g ∧ g<5 := by
  rw [unitAngleVector_inner,show Real.pi/3*((ρ-g)-ρ)= -(Real.pi/3*g) by ring,
    Real.cos_neg] at hinner
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have small (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
      (1/2:ℝ)≤Real.cos (Real.pi/3*t) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0≤Real.pi/3*t by positivity)
      (show Real.pi/3≤Real.pi by linarith [Real.pi_pos])
      (show Real.pi/3*t≤Real.pi/3 by nlinarith only [hp,ht1])
    rwa [Real.cos_pi_div_three] at h
  constructor
  · by_contra hn
    exact (not_lt_of_ge (small g hg0 (le_of_not_gt hn))) hinner
  · by_contra hn
    have h := small (6-g) (by linarith) (by linarith)
    rw [show Real.pi/3*(6-g)=2*Real.pi-Real.pi/3*g by ring,Real.cos_two_pi_sub] at h
    exact (not_lt_of_ge h) hinner

theorem exists_unit_corner_gap (ρ : ℝ) (w : Plane) (hw : ‖w‖=1)
    (hinner : inner ℝ (unitAngleVector ρ) w<1/2) :
    ∃ g : ℝ,1<g ∧ g<5 ∧ unitAngleVector (ρ-g)=w := by
  obtain ⟨θ,hθ,hphase⟩ := exists_relative_unitAngleVector w hw ρ (-6)
  have hbounds := unit_corner_gap_bounds ρ (-θ) (by linarith [hθ.2])
    (by linarith [hθ.1]) (by simpa only [sub_neg_eq_add,hphase] using hinner)
  exact ⟨-θ,hbounds.1,hbounds.2,by simpa only [sub_neg_eq_add] using hphase⟩

theorem consecutive_corner_gaps_ge_three (ρ a b : ℝ) (ha : 1<a) (hb : 1<b)
    (hfar : 1≤‖unitAngleVector (ρ-a)-
      (unitAngleVector ρ+unitAngleVector (ρ+3+b))‖) : 3≤a+b := by
  by_contra hn
  have hab : a+b<3 := lt_of_not_ge hn
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  have ha3 : a<3 := by linarith
  have hb3 : b<3 := by linarith
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have sinpos (t : ℝ) (ht0 : 0<t) (ht3 : t<3) : 0<Real.sin (Real.pi/3*t) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith only [hp,ht3])
  have cvw : cross2 (unitAngleVector ρ) (unitAngleVector (ρ+3+b))<0 := by
    rw [unitAngleVector_cross,
      show Real.pi/3*((ρ+3+b)-ρ)=Real.pi/3*b+Real.pi by ring,Real.sin_add_pi]
    exact neg_lt_zero.mpr (sinpos b hb0 hb3)
  have cuw : cross2 (unitAngleVector (ρ-a)) (unitAngleVector (ρ+3+b))<0 := by
    rw [unitAngleVector_cross,
      show Real.pi/3*((ρ+3+b)-(ρ-a))=Real.pi/3*(a+b)+Real.pi by ring,Real.sin_add_pi]
    exact neg_lt_zero.mpr (sinpos (a+b) (by linarith) hab)
  have cvu : cross2 (unitAngleVector ρ) (unitAngleVector (ρ-a))<0 := by
    rw [unitAngleVector_cross,
      show Real.pi/3*((ρ-a)-ρ)= -(Real.pi/3*a) by ring,Real.sin_neg]
    exact neg_lt_zero.mpr (sinpos a ha0 ha3)
  let r := cross2 (unitAngleVector (ρ-a)) (unitAngleVector (ρ+3+b))/
    cross2 (unitAngleVector ρ) (unitAngleVector (ρ+3+b))
  let s := cross2 (unitAngleVector ρ) (unitAngleVector (ρ-a))/
    cross2 (unitAngleVector ρ) (unitAngleVector (ρ+3+b))
  have hr : 0≤r := (div_pos_of_neg_of_neg cuw cvw).le
  have hs : 0≤s := (div_pos_of_neg_of_neg cvu cvw).le
  have hrepr : unitAngleVector (ρ-a)=r • unitAngleVector ρ+s • unitAngleVector (ρ+3+b) :=
    (cramer_reconstruct _ _ _ (ne_of_lt cvw)).symm
  rcases unit_cone_far_corner _ _ _ (unitAngleVector_norm _) (unitAngleVector_norm _)
      (unitAngleVector_norm _) (ne_of_lt cvw) r s hr hs hrepr hfar with h | h
  · rw [h,cross2_self] at cvu
    exact lt_irrefl _ cvu
  · rw [h,cross2_self] at cuw
    exact lt_irrefl _ cuw

structure CornerAngleData {n : ℕ} (G : PennyGraph n) (v : Fin n) (a : VertexRay G v) where
  phase : ℝ
  gap : ℝ
  gap_gt_one : 1<gap
  gap_lt_five : gap<5
  initial : unitAngleVector phase=G.vertexDirection v a
  terminal : unitAngleVector (phase-gap)=G.vertexDirection v (G.vertexRayRotation v a)

theorem PennyGraph.exists_corner_angle_data {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (v : Fin n) (a : VertexRay G v) : Nonempty (CornerAngleData G v a) := by
  let b := G.vertexRayRotation v a
  have hne : a.val≠b.val := by
    intro heq
    exact G.vertexRayRotation_ne_self hdegree v a (Subtype.ext heq.symm)
  have hi := G.two_step_inner_lt_half ht a.val v b.val hne a.property.symm b.property
  obtain ⟨ρ,hρ⟩ := exists_unitAngleVector (G.vertexDirection v a) (G.vertexDirection_norm v a)
  obtain ⟨g,hg1,hg5,hg⟩ := exists_unit_corner_gap ρ (G.vertexDirection v b)
    (G.vertexDirection_norm v b) (by rw [hρ]; exact hi)
  exact ⟨⟨ρ,g,hg1,hg5,hρ,hg⟩⟩

end Swanepoel
