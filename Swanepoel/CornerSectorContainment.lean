module
public import Swanepoel.PhysicalSectorArea
public import Swanepoel.FaceCornerPacking
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set

theorem unitAngleVector_cross_shift (ρ t : ℝ) :
    cross2 (unitAngleVector ρ) (unitAngleVector (ρ+t))=Real.sin (Real.pi/3*t) := by
  rw [unitAngleVector_cross,add_sub_cancel_left]

theorem radial_point_mem_full_sector (p : Plane) (ρ g t r : ℝ)
    (hg0 : 0<g) (hg6 : g<6) (ht0 : -g<t) (ht1 : t<0)
    (hr0 : 0<r) (hr1 : r<1/2) :
    p+r • unitAngleVector (ρ+t)∈
      fullClockwiseVertexSector p (unitAngleVector ρ) (unitAngleVector (ρ-g)) (1/2) := by
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have sinpos (s : ℝ) (hs0 : 0<s) (hs3 : s<3) : 0<Real.sin (Real.pi/3*s) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith only [hp,hs3])
  have sinneg (s : ℝ) (hs0 : -3<s) (hs1 : s<0) : Real.sin (Real.pi/3*s)<0 := by
    have h := sinpos (-s) (by linarith) (by linarith)
    rw [show Real.pi/3*(-s)= -(Real.pi/3*s) by ring,Real.sin_neg] at h
    linarith only [h]
  have hball : p+r • unitAngleVector (ρ+t)∈Metric.ball p (1/2:ℝ) := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      unitAngleVector_norm,Real.norm_eq_abs,abs_of_pos hr0,mul_one]
    exact hr1
  have hright (h : Real.sin (Real.pi/3*t)<0) :
      p+r • unitAngleVector (ρ+t)∈rightHalfBall (unitAngleVector ρ) p (1/2) := by
    refine ⟨hball,?_⟩
    change cross2 (unitAngleVector ρ) (p+r • unitAngleVector (ρ+t))<cross2 (unitAngleVector ρ) p
    rw [cross2_add_right,cross2_smul_right,unitAngleVector_cross_shift]
    exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hr0 h)
  have hleft (h : 0<Real.sin (Real.pi/3*(t+g))) :
      p+r • unitAngleVector (ρ+t)∈leftHalfBall (unitAngleVector (ρ-g)) p (1/2) := by
    refine ⟨hball,?_⟩
    change cross2 (unitAngleVector (ρ-g)) p<
      cross2 (unitAngleVector (ρ-g)) (p+r • unitAngleVector (ρ+t))
    rw [cross2_add_right,cross2_smul_right,unitAngleVector_cross,
      show (ρ+t)-(ρ-g)=t+g by ring]
    exact lt_add_of_pos_right _ (mul_pos hr0 h)
  rcases lt_trichotomy g 3 with hg | hg | hg
  · have hc : cross2 (unitAngleVector ρ) (unitAngleVector (ρ-g))<0 := by
      rw [unitAngleVector_cross,show (ρ-g)-ρ= -g by ring]
      exact sinneg (-g) (by linarith) (by linarith)
    rw [fullClockwiseVertexSector,ite_eq_left hc]
    exact ⟨hright (sinneg t (by linarith) ht1),hleft (sinpos (t+g) (by linarith) (by linarith))⟩
  · subst g
    have hc : cross2 (unitAngleVector ρ) (unitAngleVector (ρ-3))=0 := by
      rw [unitAngleVector_cross,show Real.pi/3*((ρ-3)-ρ)= -Real.pi by ring,Real.sin_neg,Real.sin_pi,neg_zero]
    rw [fullClockwiseVertexSector,ite_eq_right (not_lt_of_ge hc.ge),ite_eq_left hc]
    exact hright (sinneg t ht0 ht1)
  · have hc : 0<cross2 (unitAngleVector ρ) (unitAngleVector (ρ-g)) := by
      rw [unitAngleVector_cross,
        show Real.pi/3*((ρ-g)-ρ)= -(Real.pi/3*(g-3)+Real.pi) by ring,
        Real.sin_neg,Real.sin_add_pi,neg_neg]
      exact sinpos (g-3) (by linarith) (by linarith)
    rw [fullClockwiseVertexSector,ite_eq_right (not_lt_of_ge hc.le),ite_eq_right (ne_of_gt hc)]
    by_cases ht : -3<t
    · exact Or.inl (hright (sinneg t ht ht1))
    · exact Or.inr (hleft (sinpos (t+g) (by linarith) (by linarith)))

theorem cornerSectorPatch_subset_full_sector (p : Plane) (ρ g : ℝ) (hg0 : 0<g) (hg6 : g<6) :
    cornerSectorPatch p ρ g⊆
      fullClockwiseVertexSector p (unitAngleVector ρ) (unitAngleVector (ρ-g)) (1/2) := by
  intro z hz
  obtain ⟨q,hq,rfl⟩ := hz
  obtain ⟨⟨r,θ⟩,hparams,rfl⟩ := hq
  rw [sectorChart_polar]
  let t := -g/2+3*θ/Real.pi
  have hp : 0<Real.pi := Real.pi_pos
  have ht : Real.pi*t= -Real.pi*g/2+3*θ := by dsimp [t]; field_simp
  have ht0 : -g<t := by nlinarith only [ht,hparams.2.1,hp]
  have ht1 : t<0 := by nlinarith only [ht,hparams.2.2,hp]
  have hphase : ρ-g/2+3*θ/Real.pi=ρ+t := by dsimp [t]; ring
  rw [hphase]
  exact radial_point_mem_full_sector p ρ g t r hg0 hg6 ht0 ht1 hparams.1.1 hparams.1.2

theorem CornerAngleData.patch_subset_corner {n : ℕ} {G : PennyGraph n}
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    {v : Fin n} {a : VertexRay G v} (D : CornerAngleData G v a) :
    cornerSectorPatch (G.point v) D.phase D.gap⊆
      G.faceCornerRegion (G.sourceFace ⟨(v,a.val),a.property⟩) v := by
  have hsub := cornerSectorPatch_subset_full_sector (G.point v) D.phase D.gap
    (by linarith only [D.gap_gt_one]) (by linarith only [D.gap_lt_five])
  rw [D.initial,D.terminal] at hsub
  exact hsub.trans (G.rotation_half_sector_subset_corner hdegree v a)

theorem CornerAngleData.corner_area_lower {n : ℕ} {G : PennyGraph n}
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    {v : Fin n} {a : VertexRay G v} (D : CornerAngleData G v a) :
    Real.pi*D.gap/24≤volume.real (G.faceCornerRegion (G.sourceFace ⟨(v,a.val),a.property⟩) v) := by
  rw [← cornerSectorPatch_area (G.point v) D.phase D.gap
    (by linarith only [D.gap_gt_one]) (by linarith only [D.gap_lt_five])]
  exact measureReal_mono (D.patch_subset_corner hdegree) (G.faceCornerRegion_finite _ _)

end Swanepoel
