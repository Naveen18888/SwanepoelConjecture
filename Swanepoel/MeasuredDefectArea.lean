module
public import Swanepoel.CornerSectorSeparation
public import Swanepoel.CornerAreaBudget
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cornerSectorPatch_measurable (p : Plane) (ρ g : ℝ) (_hg0 : 0<g) (hg6 : g<6) :
    MeasurableSet (cornerSectorPatch p ρ g) := by
  have hp : 0<Real.pi := Real.pi_pos
  have hsub : Ioo (0:ℝ) (1/2) ×ˢ Ioo (-Real.pi*g/6) (Real.pi*g/6)⊆polarCoord.target := by
    rintro ⟨r,θ⟩ ⟨hr,hθ⟩
    exact ⟨hr.1,by nlinarith [hθ.1],by nlinarith [hθ.2]⟩
  have hopen : IsOpen (polarSector (1/2) (-Real.pi*g/6) (Real.pi*g/6)) :=
    polarCoord.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_Ioo) hsub
  exact (sectorChart p (ρ-g/2)).measurableSet_image.mpr hopen.measurableSet

def PennyGraph.actualCornerPatch {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : Set Plane :=
  cornerSectorPatch (G.point e.val.1) (G.actualCornerAngle ht hdegree e).phase
    (G.actualCornerAngle ht hdegree e).gap

theorem PennyGraph.actualCornerPatch_subset_corner {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : G.actualCornerPatch ht hdegree e⊆G.faceCornerRegion (G.sourceFace e) e.val.1 :=
  (G.actualCornerAngle ht hdegree e).patch_subset_corner hdegree

theorem PennyGraph.actualCornerPatch_measurable {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : MeasurableSet (G.actualCornerPatch ht hdegree e) :=
  cornerSectorPatch_measurable _ _ _
    (by linarith only [(G.actualCornerAngle ht hdegree e).gap_gt_one])
    (by linarith only [(G.actualCornerAngle ht hdegree e).gap_lt_five])

theorem PennyGraph.actualCornerPatch_finite {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : volume (G.actualCornerPatch ht hdegree e)≠⊤ :=
  measure_ne_top_of_subset (G.actualCornerPatch_subset_corner ht hdegree e)
    (G.faceCornerRegion_finite _ _)

theorem PennyGraph.actualCornerPatches_pairwiseDisjoint {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    Pairwise (fun e f => Disjoint (G.actualCornerPatch ht hdegree e) (G.actualCornerPatch ht hdegree f)) := by
  rintro ⟨⟨v,a⟩,hea⟩ ⟨⟨w,b⟩,heb⟩ hne
  apply Set.disjoint_left.mpr
  intro z hz1 hz2
  by_cases hvw : v=w
  · subst w
    let e : OrientedEdge G := ⟨(v,a),hea⟩
    let f : OrientedEdge G := ⟨(v,b),heb⟩
    let D := G.actualCornerAngle ht hdegree e
    let E := G.actualCornerAngle ht hdegree f
    change z∈cornerSectorPatch (G.point v) D.phase D.gap at hz1
    change z∈cornerSectorPatch (G.point v) E.phase E.gap at hz2
    have hD := cornerSectorPatch_subset_full_sector (G.point v) D.phase D.gap
      (by linarith only [D.gap_gt_one]) (by linarith only [D.gap_lt_five]) hz1
    have hE := cornerSectorPatch_subset_full_sector (G.point v) E.phase E.gap
      (by linarith only [E.gap_gt_one]) (by linarith only [E.gap_lt_five]) hz2
    rw [D.initial,D.terminal] at hD
    rw [E.initial,E.terminal] at hE
    have hrepr := hz1
    obtain ⟨q,hq,hzq⟩ := hrepr
    obtain ⟨⟨r,θ⟩,hparams,hqr⟩ := hq
    have hzr : z=G.point v+r • unitAngleVector (D.phase-D.gap/2+3*θ/Real.pi) := by
      rw [← hzq,← hqr,sectorChart_polar]
    rw [hzr] at hD hE
    have hab := D.eq_ray_of_common_radial_point hdegree E _ r hparams.1.1 hD hE
    apply hne
    exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val hab))
  · have h1 := (G.actualCornerPatch_subset_corner ht hdegree ⟨(v,a),hea⟩ hz1).2
    have h2 := (G.actualCornerPatch_subset_corner ht hdegree ⟨(w,b),heb⟩ hz2).2
    have hd1 : dist z (G.point v)<1/2 := h1
    have hd2 : dist z (G.point w)<1/2 := h2
    have hsep := G.separated v w hvw
    have htri := dist_triangle (G.point v) z (G.point w)
    rw [dist_comm (G.point v) z] at htri
    linarith only [hd1,hd2,hsep,htri]

theorem PennyGraph.face_sector_area_sum_le {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) :
    (∑ e∈G.faceIncidentDarts F,Real.pi*(G.actualCornerAngle ht hdegree e).gap/24)≤volume.real F.val := by
  have hformula (e : OrientedEdge G) : volume.real (G.actualCornerPatch ht hdegree e)=
      Real.pi*(G.actualCornerAngle ht hdegree e).gap/24 :=
    cornerSectorPatch_area _ _ _
      (by linarith only [(G.actualCornerAngle ht hdegree e).gap_gt_one])
      (by linarith only [(G.actualCornerAngle ht hdegree e).gap_lt_five])
  have hsum := measureReal_biUnion_finset (μ := (volume : Measure Plane))
    ((G.actualCornerPatches_pairwiseDisjoint ht hdegree).set_pairwise (G.faceIncidentDarts F))
    (fun e _ => G.actualCornerPatch_measurable ht hdegree e)
    (fun e _ => G.actualCornerPatch_finite ht hdegree e)
  simp_rw [hformula] at hsum
  rw [← hsum]
  apply measureReal_mono _ hF.measure_lt_top.ne
  intro z hz
  obtain ⟨e,he,hze⟩ := Set.mem_iUnion₂.mp hz
  have hface := (Finset.mem_filter.mp he).2
  have hh := (G.actualCornerPatch_subset_corner ht hdegree e hze).1
  rwa [hface] at hh

theorem PennyGraph.six_port_face_measure_lower {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) (hports : 6≤(G.faceSourcePorts F).card) :
    Real.sqrt 3/2<volume.real F.val :=
  (G.six_port_corner_area_budget ht hdegree F hports).trans_le
    (G.face_sector_area_sum_le ht hdegree F hF)

end Swanepoel
