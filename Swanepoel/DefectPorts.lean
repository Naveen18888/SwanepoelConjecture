module
public import Swanepoel.PortCounting
public import Swanepoel.FaceCounts
public import Swanepoel.EdgeSides
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def physicalEdge {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : ContactEdge G :=
  if h : e.val.1 < e.val.2 then ⟨e.val, h, e.property⟩
  else ⟨(e.val.2, e.val.1), lt_of_le_of_ne (le_of_not_gt h) e.property.ne.symm,
    e.property.symm⟩

def PennyGraph.sourceProbeDrawing {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : Finset (ContactEdge G) :=
  Finset.univ.erase (physicalEdge e)

def sourceProbeSide {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : Bool :=
  decide (e.val.2 < e.val.1)

def PennyGraph.sourceProbe {n : ℕ} (G : PennyGraph n) (e : OrientedEdge G) : Plane :=
  G.edgeSidePoint (G.sourceProbeDrawing e) (physicalEdge e) (sourceProbeSide e) (1/2)

theorem PennyGraph.sourceProbe_mem_complement {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.sourceProbe e ∈ G.drawingᶜ := by
  have he : physicalEdge e ∉ G.sourceProbeDrawing e := by simp [PennyGraph.sourceProbeDrawing]
  have hp := G.edgeSidePoint_mem_complement (G.sourceProbeDrawing e)
    (physicalEdge e) he (sourceProbeSide e) (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  simpa only [PennyGraph.sourceProbe, PennyGraph.sourceProbeDrawing,
    Finset.insert_erase (Finset.mem_univ _), G.subdrawing_univ] using hp

def PennyGraph.sourceFace {n : ℕ} (G : PennyGraph n) (e : OrientedEdge G) : PlaneFace G :=
  ⟨connectedComponentIn G.drawingᶜ (G.sourceProbe e),
    ⟨G.sourceProbe e, G.sourceProbe_mem_complement e, rfl⟩⟩

theorem PennyGraph.sourceProbe_eq_normal_offset {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) :
    G.sourceProbe e = G.edgePoint e.val.1 e.val.2 (1/2) +
      G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2) • sourceNormal e := by
  by_cases h : e.val.1 < e.val.2
  · have h' : ¬ e.val.2 < e.val.1 := not_lt_of_ge h.le
    simp only [PennyGraph.sourceProbe, PennyGraph.edgeSidePoint, sourceProbeSide,
      h', decide_false, Bool.false_eq_true, ↓reduceIte, physicalEdge, dite_eq_left h,
      sourceNormal, carriedVector, smul_neg, neg_smul]
  · have h' : e.val.2 < e.val.1 := lt_of_le_of_ne (le_of_not_gt h) e.property.ne.symm
    have hp : G.edgePoint e.val.2 e.val.1 (1/2) = G.edgePoint e.val.1 e.val.2 (1/2) := by
      simpa only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] using
        G.edgePoint_reverse e.val.1 e.val.2 (1/2)
    have hv : G.point e.val.1 - G.point e.val.2 = -carriedVector e := by
      dsimp [carriedVector]
      abel
    simp only [PennyGraph.sourceProbe, PennyGraph.edgeSidePoint, sourceProbeSide,
      h', decide_true, ↓reduceIte, physicalEdge, dite_eq_right h, hp, hv, quarterTurn_neg,
      sourceNormal, smul_neg]

theorem PennyGraph.sourceProbe_offset_pos {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) :
    0 < G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2) := by
  exact (G.edgeClearance_spec (G.sourceProbeDrawing e) (physicalEdge e)
    (by simp [PennyGraph.sourceProbeDrawing]) (by norm_num) (by norm_num)).1

def PennyGraph.faceSourcePorts {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ G.sourceFace e = F)

def PennyGraph.familySourcePorts {n : ℕ} (G : PennyGraph n) (A : Finset (PlaneFace G)) :
    Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ G.sourceFace e ∈ A)

theorem PennyGraph.faceSourcePorts_disjoint {n : ℕ} (G : PennyGraph n)
    {F H : PlaneFace G} (hne : F ≠ H) :
    Disjoint (G.faceSourcePorts F) (G.faceSourcePorts H) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hne ((Finset.mem_filter.mp he).2.2.symm.trans (Finset.mem_filter.mp hf).2.2)

theorem PennyGraph.familySourcePorts_card {n : ℕ} (G : PennyGraph n)
    (A : Finset (PlaneFace G)) :
    (G.familySourcePorts A).card = ∑ F ∈ A, (G.faceSourcePorts F).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := G.sourceFace) (s := G.familySourcePorts A) (t := A)
    (fun e he => (Finset.mem_filter.mp he).2.2)
  rw [h]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  ext e
  simp only [PennyGraph.familySourcePorts, PennyGraph.faceSourcePorts,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hs, _⟩, he⟩
    exact ⟨hs, he⟩
  · rintro ⟨hs, he⟩
    exact ⟨⟨hs, he ▸ hF⟩, he⟩

theorem PennyGraph.familySourcePorts_card_le {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (A : Finset (PlaneFace G)) :
    ∑ F ∈ A, (G.faceSourcePorts F).card ≤ 2 * Fintype.card (TrackComponent G) := by
  rw [← G.familySourcePorts_card A, ← spine_source_count G ht]
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1⟩

def PennyGraph.defectPlaneFaces {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Finset (PlaneFace G) :=
  (G.defectFaces ht).image (fun F => ⟨F.val, F.property.1⟩)

theorem PennyGraph.defectPlaneFaces_card {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) : (G.defectPlaneFaces ht).card = G.faceDefectCount ht := by
  rw [PennyGraph.defectPlaneFaces, Finset.card_image_of_injective]
  · rfl
  · intro F H he
    exact Subtype.ext (congrArg (fun F : PlaneFace G => F.val) he)

theorem PennyGraph.effective_nonneg_of_defect_source_ports {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hports : ∀ F ∈ G.defectPlaneFaces ht, 4 ≤ (G.faceSourcePorts F).card) :
    0 ≤ (Fintype.card (TrackComponent G) : ℤ) - 2 * G.faceDefectCount ht := by
  have hlo : 4 * (G.defectPlaneFaces ht).card ≤
      ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card := by
    calc
      _ = ∑ _ ∈ G.defectPlaneFaces ht, 4 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hports
  rw [G.defectPlaneFaces_card ht] at hlo
  have hhi := G.familySourcePorts_card_le ht (G.defectPlaneFaces ht)
  have hnat : 2 * G.faceDefectCount ht ≤ Fintype.card (TrackComponent G) := by omega
  exact sub_nonneg.mpr (by exact_mod_cast hnat)

end Swanepoel
