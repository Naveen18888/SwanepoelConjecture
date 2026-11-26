module
public import Swanepoel.Combinatorics
public import Swanepoel.PentagonConeAccounting
public import Swanepoel.UnitCircleCones
public import Swanepoel.PentagonFirstCrossing
public import Swanepoel.SpokeCrossingLabels
public import Swanepoel.PentagonCrossingCones
public import Swanepoel.PentagonMixedEstimate
public import Swanepoel.QuadraticAreaBridge
public import Swanepoel.Lemma37
public import Swanepoel.L38Lemma
public import Swanepoel.RecursiveCutAccounting
public import Swanepoel.CyclicBlock
public import Swanepoel.Lemma31
public import Swanepoel.Quantitative
public import Swanepoel.Decomposition
public import Swanepoel.Foundation
public import Swanepoel.Rhombi
public import Swanepoel.RhombusArea
public import Swanepoel.Cells
public import Swanepoel.TrackComponents
public import Swanepoel.CutArithmetic
public import Swanepoel.PositiveSpines
public import Swanepoel.CompleteSpines
public import Swanepoel.DefectFree
public import Swanepoel.FaceCounts
public import Swanepoel.EulerPreparation
public import Swanepoel.EulerStart
public import Swanepoel.EulerForest
public import Swanepoel.CycleSeparation
public import Swanepoel.PolygonReduction
public import Swanepoel.PolygonSeparationProof
public import Swanepoel.TrackSimplicity
public import Swanepoel.DefectPortRealization
public import Swanepoel.TrackClassification
public import Swanepoel.DefectBoundary
public import Swanepoel.FacePortLowerBound
public import Swanepoel.DefectFreeCanonical
public import Swanepoel.DisjointReduction
public import Swanepoel.SemicirclePorts
public import Swanepoel.FacePortCycles
public import Swanepoel.FacePortFourCycle
public import Swanepoel.FacePortFive
public import Swanepoel.ConnectedBounds
public import Swanepoel.TerminalPortConservation
public import Swanepoel.SemicircleFaceGeometry
public import Swanepoel.QuadraticBoundaryCase
public import Swanepoel.JoinClosedFamilies
public import Swanepoel.JoinClosedDecomposition
public import Swanepoel.JoinClosedCrossings
public import Swanepoel.BoundaryPortPairing
public import Swanepoel.JoinClosedPentagons
public import Swanepoel.TrackCut
public import Swanepoel.TrackCutTransitions
public import Swanepoel.TrackCutRealization
public import Swanepoel.TrackCutPreservation
public import Swanepoel.TrackCutCounting
public import Swanepoel.TrackCutSources
public import Swanepoel.TrackCutOuterClosure
public import Swanepoel.TrackCutWindingPolyline
public import Swanepoel.TrackCutWindingClosure
public import Swanepoel.TrackCutWindingDefects
public import Swanepoel.TrackCutWindingJump
public import Swanepoel.TrackCutWindingCompatibilityLoop
public import Swanepoel.TerminalDisplacement
public import Swanepoel.TerminalWalkIntegral
public import Swanepoel.DisplacementPotential
public import Swanepoel.RhombusDisplacementPotential
public import Swanepoel.PolygonArea
public import Swanepoel.PolygonCompression
public import Swanepoel.PolygonIsoperimetry
public import Swanepoel.PolygonIsoperimetrySpectral
public import Swanepoel.PolygonIsoperimetryArea
public import Swanepoel.PolygonIsoperimetryList
public import Swanepoel.FaceBoundaryOrder
public import Swanepoel.FaceBoundaryOrderOrbit
public import Swanepoel.FaceBoundaryPermutation
public import Swanepoel.FaceBoundaryPermutationCycles
public import Swanepoel.FaceBoundaryCapReduction
public import Swanepoel.MonotoneCapChain
public import Swanepoel.MonotoneCapChainSides
public import Swanepoel.UnitCapGeometry
public import Swanepoel.UnitCapPenny
public import Swanepoel.RayGeneric
public import Swanepoel.FaceDirectionalSupport
public import Swanepoel.FaceDualConnectivity
public import Swanepoel.FaceDualConnectivityLinear
public import Swanepoel.DefectTwoSemicirclePorts
public import Swanepoel.FivePortBoundaryCycle
public import Swanepoel.FivePortBoundarySimple
public import Swanepoel.DefectSemicircleTracks
public import Swanepoel.SemicircleConeGeometry
public import Swanepoel.CrossingPortCones
public import Swanepoel.FaceDisplacementCurl
public import Swanepoel.ContactGradient
public import Swanepoel.ContactGradientOrientations
public import Swanepoel.FacialCycleBasis
public import Swanepoel.FacialCycleBasisExact
public import Swanepoel.RetainedMap
public import Swanepoel.SectorPortCounting
public import Swanepoel.SectorConstruction
public import Swanepoel.HalfAnchorCounting
public import Swanepoel.HalfSystemBankRealization
public import Swanepoel.BankBound
public import Swanepoel.QuadraticGeometryReduction
public import Swanepoel.RetainedAreaDecomposition
public import Swanepoel.VertexSectorClearance
public import Swanepoel.DefectHalfOpenCone
public import Swanepoel.PentagonFaceBoundary
public import Swanepoel.PentagonConeCount
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

noncomputable section
namespace Swanepoel

section
attribute [local instance] Classical.propDecidable

theorem PennyGraph.CyclicBlock.lemma_3_7 {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.lemma_3_7 ht hb.2.1 (G.other_neighbor_of_delete_connected hb.1 hb.2.2)

theorem PennyGraph.CyclicBlock.lemma_3_8 {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) {cut : TrackComponent G}
    (B : OrdinaryCutBanks G cut) (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) :
    (B.canonicalHalfSystem ht side).HighBankBound :=
  B.canonicalHalfSystem_lemma_3_8 ht hb.2.1
    (G.other_neighbor_of_delete_connected hb.1 hb.2.2) hcut side

theorem PennyGraph.CyclicBlock.quadratic_bound_of_face_measure_identity {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree)
    (hidentity : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      G.faceSignedArea G.point F=MeasureTheory.volume.real F.val) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_face_measure_identity ht hb.2.1
    (G.other_neighbor_of_delete_connected hb.1 hb.2.2) hidentity

theorem PennyGraph.CyclicBlock.quadratic_bound_of_large_face_area {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree)
    (hlarge : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      Real.sqrt 3/2≤G.faceSignedArea G.point F) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_large_face_area ht hb.2.1
    (G.other_neighbor_of_delete_connected hb.1 hb.2.2) hlarge

theorem PennyGraph.CyclicBlock.defect_half_open_120_cone_count {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F∈G.defectPlaneFaces ht) (b : Plane) (hbunit : ‖b‖=1) :
    ((G.faceSourcePorts F).filter (fun e => HalfOpen120Cone b (sourceNormal e))).card+3≤
      (G.faceSourcePorts F).card :=
  G.defect_half_open_120_cone_count ht F hF (G.other_neighbor_of_delete_connected hb.1 hb.2.2) b hbunit

theorem PennyGraph.CyclicBlock.five_port_internal_crossings_zero {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F∈G.defectPlaneFaces ht) (hfive : (G.faceSourcePorts F).card=5) :
    G.familyInternalCrossings ht {F}=0 :=
  G.five_port_internal_crossings_zero ht F hF (G.other_neighbor_of_delete_connected hb.1 hb.2.2) hfive

theorem PennyGraph.CyclicBlock.five_port_face_area_lower {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F∈G.defectPlaneFaces ht) (hfive : (G.faceSourcePorts F).card=5) :
    Real.sqrt 3/2<G.faceSignedArea G.point F :=
  G.five_port_face_area_lower ht F hF (G.other_neighbor_of_delete_connected hb.1 hb.2.2) hfive

end

theorem PennyGraph.CyclicBlock.defect_meets_semicircle {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F ∈ G.defectPlaneFaces ht) (v : Plane) (hv : v ≠ 0) :
    ∃ e ∈ G.faceSourcePorts F, 0 < inner ℝ v (sourceNormal e) := by
  exact G.defect_meets_semicircle_of_delete_connected ht hb.1 hb.2.2 F hF v hv

theorem PennyGraph.CyclicBlock.defect_two_semicircle_ports {n : ℕ} {G : PennyGraph n}
    (hb : G.CyclicBlock) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F∈G.defectPlaneFaces ht) (v : Plane) (hv : v≠0) :
    2≤((G.faceSourcePorts F).filter (fun e => 0 < inner ℝ v (sourceNormal e))).card :=
  G.defect_two_semicircle_ports_of_delete_connected ht hb.1 hb.2.2 F hF v hv

structure BlockCertificate {n : ℕ} (G : PennyGraph n) where
  triangleFree : G.TriangleFree
  cyclicBlock : G.CyclicBlock

def BlockCertificate.halves {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) : List HalfSystem :=
  G.canonicalCutHalves C.triangleFree

theorem BlockCertificate.half_realizations {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    ∀ H∈C.halves,∃ cut : TrackComponent G,∃ B : OrdinaryCutBanks G cut,
      cut∈G.ordinaryTrackComponents ∧ ∃ side : Bool,Nonempty (H.BankRealization B C.triangleFree side) :=
  fun H hH => G.canonicalCutHalves_realized C.triangleFree C.cyclicBlock.2.1 H hH

theorem BlockCertificate.halves_complete {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G)
    (c : {c : TrackComponent G // c∈G.admissibleOrdinaryCuts}) (side : Bool) :
    (G.chosenCutBanks C.triangleFree c).canonicalHalfSystem C.triangleFree side∈C.halves :=
  (G.mem_canonicalCutHalves C.triangleFree _).mpr ⟨c,side,rfl⟩

def BlockCertificate.ordinaryComponents {n : ℕ} {G : PennyGraph n}
    (_C : BlockCertificate G) : Finset (TrackComponent G) := G.ordinaryTrackComponents

def BlockCertificate.faceDefects {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) : ℕ :=
  G.faceDefectCount C.triangleFree

theorem BlockCertificate.faceEuler {n : ℕ} {G : PennyGraph n}
    (C : BlockCertificate G) : G.FaceEuler :=
  G.faceEuler_of_connected C.cyclicBlock.2.1

theorem BlockCertificate.effective_nonneg {n : ℕ} {G : PennyGraph n}
    (C : BlockCertificate G) :
    0≤(Fintype.card (TrackComponent G) : ℤ)-2*G.faceDefectCount C.triangleFree :=
  G.geometric_effective_nonneg C.triangleFree

theorem BlockCertificate.euler {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+C.faceDefects)=1 :=
  G.euler_with_defects C.triangleFree C.faceEuler

def BlockCertificate.counts {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) : BlockCounts :=
  geometricBlockCounts G C.triangleFree C.faceDefects C.euler C.effective_nonneg

theorem BlockCertificate.vertices_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.n=n := rfl

theorem BlockCertificate.edges_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.m=G.edgeCount := rfl

theorem BlockCertificate.rhombi_count {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.q=Fintype.card (RhombusSet G) := rfl

theorem BlockCertificate.rhombic_faces_count {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.q=(G.rhombicFaces C.triangleFree).card :=
  (G.rhombicFaces_card C.triangleFree).symm

theorem BlockCertificate.defects_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.f=C.faceDefects := rfl

theorem BlockCertificate.total_tracks_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.T=Fintype.card (TrackComponent G) := rfl

theorem BlockCertificate.effective_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.x=(componentSystem G C.triangleFree C.ordinaryComponents C.faceDefects).K+
      (componentSystem G C.triangleFree C.ordinaryComponents C.faceDefects).t :=
  (componentSystem_effective_count G C.triangleFree C.ordinaryComponents C.faceDefects).symm

def BlockCertificate.tracks {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) : TrackSystem :=
  componentSystem G C.triangleFree C.ordinaryComponents C.faceDefects

theorem BlockCertificate.lemma_3_1 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.tracks.DisjointBound :=
  G.lemma_3_1 C.triangleFree C.cyclicBlock.2.1

theorem BlockCertificate.K_nonneg {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    0≤C.tracks.K := G.canonical_componentSystem_K_nonneg C.triangleFree

theorem BlockCertificate.lemma_3_3 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.tracks.NoTriple :=
  componentSystem_noTriple G C.triangleFree C.ordinaryComponents C.faceDefects

theorem BlockCertificate.lemma_3_7 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.tracks.QuadraticBound :=
  C.cyclicBlock.lemma_3_7 C.triangleFree

theorem BlockCertificate.lemma_3_4 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.tracks.CrossingPairBound :=
  G.canonical_crossing_pair_bound C.triangleFree
    (G.other_neighbor_of_delete_connected C.cyclicBlock.1 C.cyclicBlock.2.2)

theorem BlockCertificate.lemma_3_5 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    ∀ H∈C.halves, H.NonAnchorBound := by
  intro H hH
  obtain ⟨cut,B,hcut,side,⟨R⟩⟩ := C.half_realizations H hH
  exact R.nonAnchorBound
    (G.other_neighbor_of_delete_connected C.cyclicBlock.1 C.cyclicBlock.2.2) hcut

theorem BlockCertificate.lemma_3_6 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    ∀ H∈C.halves, H.BankBound := by
  intro H hH
  obtain ⟨cut,B,hcut,side,⟨R⟩⟩ := C.half_realizations H hH
  exact R.bankBound

theorem BlockCertificate.lemma_3_8 {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    ∀ H∈C.halves, H.HighBankBound := by
  intro H hH
  obtain ⟨cut,B,hcut,side,⟨R⟩⟩ := C.half_realizations H hH
  exact R.highBankBound C.cyclicBlock.2.1
    (G.other_neighbor_of_delete_connected C.cyclicBlock.1 C.cyclicBlock.2.2) hcut

theorem BlockCertificate.rhombi_eq {n : ℕ} {G : PennyGraph n} (C : BlockCertificate G) :
    C.counts.q=C.tracks.q :=
  C.rhombi_count.trans (componentSystem_q_eq_rhombi G C.triangleFree
    C.ordinaryComponents C.faceDefects).symm

theorem defect_free_block_certificate {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hb : G.CyclicBlock) (_hf : G.faceDefectCount ht=0) :
    Nonempty (BlockCertificate G) := by
  refine ⟨{
    triangleFree := ht
    cyclicBlock := hb
  }⟩

theorem cyclic_block_certificate {n : ℕ} (G : PennyGraph n)
    (htriangle : G.TriangleFree) (hblock : G.CyclicBlock) :
    Nonempty (BlockCertificate G) := by
  exact ⟨{triangleFree := htriangle,cyclicBlock := hblock}⟩

theorem certificate_bound {n : ℕ} (G : PennyGraph n) (C : BlockCertificate G) :
    (G.edgeCount : ℤ) ≤ extremalValue n := by
  have h := C.tracks.rhombi_bound C.lemma_3_3 C.lemma_3_4 C.lemma_3_1
  have hq : (C.counts.q : ℤ) + C.counts.f ≤ N C.counts.x := by
    rw [C.rhombi_eq,C.defects_eq,C.effective_eq]
    simpa only [BlockCertificate.tracks,componentSystem] using h
  have hb := block_bound C.counts hq
  simpa [C.vertices_eq, C.edges_eq] using hb

theorem cyclic_block_upper_bound {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hb : G.CyclicBlock) :
    (G.edgeCount : ℤ) ≤ extremalValue n := by
  obtain ⟨C⟩ := cyclic_block_certificate G ht hb
  exact certificate_bound G C

theorem assemble_blocks
    (hblock : ∀ n, ∀ G : PennyGraph n, G.TriangleFree → G.CyclicBlock →
      (G.edgeCount : ℤ) ≤ extremalValue n) : UpperBound := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn G ht
  by_cases hsmall : n ≤ 2
  · exact small_graph_upper_bound G hn hsmall
  have hn3 : 3 ≤ n := by omega
  by_cases hcyclic : G.CyclicBlock
  · exact hblock n G ht hcyclic
  have hsplit : Nonempty (VertexSplit G) := by
    by_cases hconn : G.graph.Connected
    · have hd : ¬ ∀ v : Fin n, (G.graph.induce {w | w ≠ v}).Connected :=
        fun hd => hcyclic ⟨hn3, hconn, hd⟩
      obtain ⟨v, hv⟩ := not_forall.mp hd
      exact cut_vertex_split G hn3 v hv
    · exact disconnected_split G hn hconn
  obtain ⟨C⟩ := hsplit
  have hlpos : 1 ≤ C.left.card := C.left_nonempty.card_pos
  have hrpos : 1 ≤ C.right.card := C.right_nonempty.card_pos
  have hl := ih C.left.card C.left_smaller hlpos (G.restrict C.left)
    (G.restrict_triangleFree C.left ht)
  have hr := ih C.right.card C.right_smaller hrpos (G.restrict C.right)
    (G.restrict_triangleFree C.right ht)
  have he : (G.edgeCount : ℤ) = ((G.restrict C.left).edgeCount : ℤ) +
      (G.restrict C.right).edgeCount := by exact_mod_cast C.edges
  rcases C.sizes with hs | hs
  · have hf := extremal_disjoint C.left.card C.right.card
    rw [hs] at hf
    omega
  · have hf := extremal_one_vertex C.left.card C.right.card n hlpos hrpos (by omega)
    omega

theorem upper_bound : UpperBound := assemble_blocks (fun _ G ht hb =>
  cyclic_block_upper_bound G ht hb)

end Swanepoel
