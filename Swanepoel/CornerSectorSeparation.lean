module
public import Swanepoel.CornerSectorContainment
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

private theorem corner_right_cross (p u x : Plane) {r : ℝ} (hr : 0<r)
    (h : p+r • x∈rightHalfBall u p (1/2)) : cross2 u x<0 := by
  have hh : cross2 u (p+r • x)<cross2 u p := h.2
  rw [cross2_add_right,cross2_smul_right] at hh
  by_contra hn
  have hm := mul_nonneg hr.le (le_of_not_gt hn)
  linarith only [hh,hm]

private theorem corner_left_cross (p u x : Plane) {r : ℝ} (hr : 0<r)
    (h : p+r • x∈leftHalfBall u p (1/2)) : 0<cross2 u x := by
  have hh : cross2 u p<cross2 u (p+r • x) := h.2
  rw [cross2_add_right,cross2_smul_right] at hh
  by_contra hn
  have hm := mul_nonpos_of_nonneg_of_nonpos hr.le (le_of_not_gt hn)
  linarith only [hh,hm]

theorem full_sector_point_between (p u w x : Plane) (hne : u≠w)
    {r : ℝ} (hr : 0<r)
    (h : p+r • x∈fullClockwiseVertexSector p u w (1/2)) : ClockwiseRayBetween u w x := by
  unfold fullClockwiseVertexSector at h
  unfold ClockwiseRayBetween
  rw [ite_eq_right hne]
  split_ifs with hc hz
  · rw [ite_eq_left hc] at h
    exact ⟨corner_right_cross p u x hr h.1,corner_left_cross p w x hr h.2⟩
  · rw [ite_eq_right hc,ite_eq_left hz] at h
    exact corner_right_cross p u x hr h
  · rw [ite_eq_right hc,ite_eq_right hz] at h
    exact h.elim (fun h => Or.inl (corner_right_cross p u x hr h))
      (fun h => Or.inr (corner_left_cross p w x hr h))

theorem full_sector_member_forces_phase (p : Plane) (Φ ρ g r : ℝ)
    (_hρ0 : 0<ρ) (hρ6 : ρ≤6) (hg0 : 0<g) (hg6 : g<6) (hr : 0<r)
    (hz : p+r • unitAngleVector Φ∈fullClockwiseVertexSector p
      (unitAngleVector (Φ+ρ)) (unitAngleVector (Φ+ρ-g)) (1/2)) : ρ<g := by
  by_contra hn
  have hgρ : g≤ρ := le_of_not_gt hn
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have sinnonneg (s : ℝ) (hs0 : 0≤s) (hs3 : s≤3) : 0≤Real.sin (Real.pi/3*s) :=
    Real.sin_nonneg_of_mem_Icc ⟨by positivity,by nlinarith only [hp,hs3]⟩
  have sinpos (s : ℝ) (hs0 : 0<s) (hs3 : s<3) : 0<Real.sin (Real.pi/3*s) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith only [hp,hs3])
  have hright (h : p+r • unitAngleVector Φ∈rightHalfBall (unitAngleVector (Φ+ρ)) p (1/2)) : ρ<3 := by
    have hh := corner_right_cross p (unitAngleVector (Φ+ρ)) (unitAngleVector Φ) hr h
    rw [unitAngleVector_cross,
      show Real.pi/3*(Φ-(Φ+ρ))= -(Real.pi/3*ρ) by ring,Real.sin_neg] at hh
    by_contra hn3
    have hs := sinnonneg (6-ρ) (by linarith) (by linarith)
    rw [show Real.pi/3*(6-ρ)=2*Real.pi-Real.pi/3*ρ by ring,Real.sin_two_pi_sub] at hs
    linarith only [hh,hs]
  have hnotLeft (hρg : ρ-g≤3) :
      ¬p+r • unitAngleVector Φ∈leftHalfBall (unitAngleVector (Φ+ρ-g)) p (1/2) := by
    intro h
    have hh := corner_left_cross p (unitAngleVector (Φ+ρ-g)) (unitAngleVector Φ) hr h
    rw [unitAngleVector_cross,
      show Real.pi/3*(Φ-(Φ+ρ-g))= -(Real.pi/3*(ρ-g)) by ring,Real.sin_neg] at hh
    have hs := sinnonneg (ρ-g) (by linarith) hρg
    linarith only [hh,hs]
  rcases lt_trichotomy g 3 with hg | hg | hg
  · have hc : cross2 (unitAngleVector (Φ+ρ)) (unitAngleVector (Φ+ρ-g))<0 := by
      rw [unitAngleVector_cross,
        show Real.pi/3*((Φ+ρ-g)-(Φ+ρ))= -(Real.pi/3*g) by ring,Real.sin_neg]
      exact neg_lt_zero.mpr (sinpos g hg0 hg)
    rw [fullClockwiseVertexSector,ite_eq_left hc] at hz
    have hρ := hright hz.1
    exact hnotLeft (by linarith) hz.2
  · subst g
    have hc : cross2 (unitAngleVector (Φ+ρ)) (unitAngleVector (Φ+ρ-3))=0 := by
      rw [unitAngleVector_cross,
        show Real.pi/3*((Φ+ρ-3)-(Φ+ρ))= -Real.pi by ring,Real.sin_neg,Real.sin_pi,neg_zero]
    rw [fullClockwiseVertexSector,ite_eq_right (not_lt_of_ge hc.ge),ite_eq_left hc] at hz
    linarith only [hright hz,hgρ]
  · have hc : 0<cross2 (unitAngleVector (Φ+ρ)) (unitAngleVector (Φ+ρ-g)) := by
      rw [unitAngleVector_cross,
        show Real.pi/3*((Φ+ρ-g)-(Φ+ρ))= -(Real.pi/3*(g-3)+Real.pi) by ring,
        Real.sin_neg,Real.sin_add_pi,neg_neg]
      exact sinpos (g-3) (by linarith) (by linarith)
    rw [fullClockwiseVertexSector,ite_eq_right (not_lt_of_ge hc.le),ite_eq_right (ne_of_gt hc)] at hz
    rcases hz with hz | hz
    · linarith only [hright hz,hgρ,hg]
    · exact hnotLeft (by linarith) hz

theorem CornerAngleData.eq_ray_of_common_radial_point {n : ℕ} {G : PennyGraph n}
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    {v : Fin n} {a b : VertexRay G v} (D : CornerAngleData G v a) (E : CornerAngleData G v b)
    (Φ r : ℝ) (hr : 0<r)
    (hD : G.point v+r • unitAngleVector Φ∈fullClockwiseVertexSector (G.point v)
      (G.vertexDirection v a) (G.vertexDirection v (G.vertexRayRotation v a)) (1/2))
    (hE : G.point v+r • unitAngleVector Φ∈fullClockwiseVertexSector (G.point v)
      (G.vertexDirection v b) (G.vertexDirection v (G.vertexRayRotation v b)) (1/2)) : a=b := by
  have lift (c : VertexRay G v) (C : CornerAngleData G v c)
      (hz : G.point v+r • unitAngleVector Φ∈fullClockwiseVertexSector (G.point v)
        (G.vertexDirection v c) (G.vertexDirection v (G.vertexRayRotation v c)) (1/2)) :
      ∃ ρ : ℝ,0<ρ ∧ ρ≤6 ∧ ρ<C.gap ∧
        unitAngleVector (Φ+ρ)=G.vertexDirection v c ∧
        unitAngleVector (Φ+ρ-C.gap)=G.vertexDirection v (G.vertexRayRotation v c) := by
    obtain ⟨ρ,hρ,hbase⟩ := exists_relative_unitAngleVector (G.vertexDirection v c)
      (G.vertexDirection_norm v c) Φ 0
    have hend := unitAngleVector_add_eq_of_eq (hbase.trans C.initial.symm) (-C.gap)
    have hterminal : unitAngleVector (Φ+ρ-C.gap)=G.vertexDirection v (G.vertexRayRotation v c) := by
      simpa only [← sub_eq_add_neg,C.terminal] using hend
    have hρgap := full_sector_member_forces_phase (G.point v) Φ ρ C.gap r
      hρ.1 (by simpa using hρ.2) (by linarith only [C.gap_gt_one])
      (by linarith only [C.gap_lt_five]) hr (by rwa [hbase,hterminal])
    exact ⟨ρ,hρ.1,by simpa using hρ.2,hρgap,hbase,hterminal⟩
  obtain ⟨ρ,hρ0,hρ6,hρgap,hρbase,hρend⟩ := lift a D hD
  obtain ⟨σ,hσ0,hσ6,hσgap,hσbase,hσend⟩ := lift b E hE
  have least (c d : VertexRay G v) (C : CornerAngleData G v c) (τ υ : ℝ)
      (hτgap : τ<C.gap) (hυ0 : 0<υ)
      (hbase : unitAngleVector (Φ+τ)=G.vertexDirection v c)
      (hend : unitAngleVector (Φ+τ-C.gap)=G.vertexDirection v (G.vertexRayRotation v c))
      (hother : unitAngleVector (Φ+υ)=G.vertexDirection v d) : τ≤υ := by
    by_contra hn
    have hlt : υ<τ := lt_of_not_ge hn
    have hpoint := radial_point_mem_full_sector (G.point v) (Φ+τ) C.gap (υ-τ) (1/4)
      (by linarith only [C.gap_gt_one]) (by linarith only [C.gap_lt_five])
      (by linarith only [hτgap,hυ0]) (by linarith only [hlt]) (by norm_num) (by norm_num)
    rw [show (Φ+τ)+(υ-τ)=Φ+υ by ring,hbase,hend,hother] at hpoint
    have hbetween := full_sector_point_between (G.point v) (G.vertexDirection v c)
      (G.vertexDirection v (G.vertexRayRotation v c)) (G.vertexDirection v d)
      (fun h => (G.vertexRayRotation_ne_self hdegree v c)
        (G.vertexDirection_injective v h).symm) (by norm_num : (0:ℝ)<1/4) hpoint
    exact clockwiseRayPermutation_empty (G.vertexDirection v) (G.vertexDirection_norm v)
      (G.vertexDirection_injective v) c d hbetween
  have hρσ := le_antisymm (least a b D ρ σ hρgap hσ0 hρbase hρend hσbase)
    (least b a E σ ρ hσgap hρ0 hσbase hσend hρbase)
  apply G.vertexDirection_injective v
  rw [← hρbase,← hσbase,hρσ]

end Swanepoel
