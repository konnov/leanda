import TendermintSingle.Proofs.Basic
import Mathlib.Data.Finset.Max

namespace tendermint_single_indinv

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Section B (`InitInd`) of the TLAPS proof. -/
theorem typed_ind_inv_init {s : State}
    (hmodel : model_assumptions s) (hinit : init s) :
    typed_ind_inv s := by
  rw [typed_ind_inv_iff, ind_inv_iff_named]
  unfold model_assumptions at hmodel
  rcases hmodel with
    ⟨hNgt, hNeq, hfault, hdisj, hNcard, hN0, hT0, hmax,
      hnil, ⟨valid, hvalid⟩⟩
  unfold init at hinit
  rcases hinit with
    ⟨hkr, hr, hks, hs, hkd, hd, hklv, hlv, hklr, hlr,
      hkvv, hvv, hkvr, hvr, hkmp, hmp, hkmv, hmv, hkmc, hmc, haction⟩
  constructor
  · unfold ind_type_ok
    simp only [hkr, hks, hkd, hklv, hklr, hkvv, hkvr, hkmp, hkmv,
      hkmc, true_and]
    repeat' apply And.intro
    · intro p hp
      rw [hr p hp]
      simp only [Finset.mem_Icc]
      omega
    · intro p hp
      rw [hs p hp]
      simp
    · intro p hp
      rw [hd p hp]
      simp
    · intro p hp
      rw [hlv p hp]
      simp
    · intro p hp
      rw [hlr p hp]
      simp
    · intro p hp
      rw [hvv p hp]
      simp
    · intro p hp
      rw [hvr p hp]
      simp
    · intro r hrange m hm
      rw [hmp r hrange] at hm
      simp at hm
    · intro r hrange m hm
      rw [hmp r hrange] at hm
      simp at hm
    · intro r hrange m hm
      rw [hmv r hrange] at hm
      simp at hm
    · intro r hrange m hm
      rw [hmv r hrange] at hm
      simp at hm
    · intro r hrange m hm
      rw [hmc r hrange] at hm
      simp at hm
    · intro r hrange m hm
      rw [hmc r hrange] at hm
      simp at hm
    · simp [haction]
  · constructor
    · unfold all_no_future_messages_sent
      intro p hp
      rw [hr p hp, hs p hp]
      constructor
      · constructor
        · right
          intro m hm
          rw [hmp 0 (by simp [Finset.mem_Icc, hmax])] at hm
          simp at hm
        · constructor
          · right; right; right
            intro m hm
            rw [hmv 0 (by simp [Finset.mem_Icc, hmax])] at hm
            simp at hm
          · right; right
            intro m hm
            rw [hmc 0 (by simp [Finset.mem_Icc, hmax])] at hm
            simp at hm
      · intro r hrange
        have hrange' : r ∈ Finset.Icc 0 s.MaxRound :=
          (Finset.mem_filter.mp hrange).1
        constructor
        · intro m hm
          rw [hmp r hrange'] at hm
          simp at hm
        · constructor
          · intro m hm
            rw [hmv r hrange'] at hm
            simp at hm
          · intro m hm
            rw [hmc r hrange'] at hm
            simp at hm
    · constructor
      · unfold all_if_in_prevote_then_sent_prevote
        intro p hp
        rw [hs p hp]
        simp
      · constructor
        · unfold all_if_in_precommit_then_sent_precommit
          intro p hp
          rw [hs p hp]
          simp
        · constructor
          · unfold all_if_in_decided_then_received_proposal
            intro p hp
            rw [hs p hp]
            simp
          · constructor
            · unfold all_if_in_decided_then_received_two_thirds
              intro p hp
              rw [hs p hp]
              simp
            · constructor
              · unfold all_if_in_decided_then_valid_decision
                intro p hp
                rw [hs p hp, hd p hp]
                simp [hnil]
              · constructor
                · unfold all_locked_round_iff_locked_value
                  intro p hp
                  rw [hlr p hp, hlv p hp]
                · constructor
                  · unfold all_valid_round_iff_valid_value
                    intro p hp
                    rw [hvr p hp, hvv p hp]
                  · constructor
                    · unfold all_valid_and_locked_round_bounded
                      intro p hp
                      rw [hvr p hp, hlr p hp, hr p hp]
                      omega
                    · constructor
                      · unfold all_if_valid_round_then_two_thirds_prevotes
                        intro p hp
                        rw [hvr p hp]
                        simp
                      · constructor
                        · unfold all_if_locked_round_then_sent_commit
                          intro p hp
                          rw [hlr p hp]
                          simp
                        · constructor
                          · unfold all_latest_precommit_has_locked_round
                            intro p hp
                            left
                            refine ⟨hlr p hp, hlv p hp, ?_⟩
                            intro r hrange m hm
                            rw [hmc r hrange] at hm
                            simp at hm
                          · constructor
                            · unfold all_if_sent_prevote_then_received_proposal_or_two_thirds
                              intro r hrange m hm
                              rw [hmv r hrange] at hm
                              simp at hm
                            · constructor
                              · unfold if_sent_precommit_then_sent_prevote
                                intro r hrange m hm
                                rw [hmc r hrange] at hm
                                simp at hm
                              · constructor
                                · unfold if_sent_precommit_then_received_two_thirds
                                  intro r hrange m hm
                                  rw [hmc r hrange] at hm
                                  simp at hm
                                · constructor
                                  · unfold all_no_equivocation_by_correct
                                    intro r hrange
                                    constructor
                                    · refine ⟨valid, hvalid, -1, by simp, ?_⟩
                                      intro m hm
                                      rw [hmp r hrange] at hm
                                      simp at hm
                                    · constructor
                                      · intro p hp
                                        refine ⟨-1, by simp, ?_⟩
                                        intro m hm _
                                        rw [hmv r hrange] at hm
                                        simp at hm
                                      · intro p hp
                                        refine ⟨-1, by simp, ?_⟩
                                        intro m hm _
                                        rw [hmc r hrange] at hm
                                        simp at hm
                                  · constructor
                                    · unfold precommits_lock_value
                                      intro r hrange v hv
                                      left
                                      rw [hmc r hrange]
                                      simp
                                      omega
                                    · constructor
                                      · unfold precommit_locks_later_prevotes
                                        intro p hp r hrange v hv r' hrange' himp
                                        rw [hmc r hrange] at himp
                                        simp at himp
                                      · constructor
                                        · unfold all_locked_proposer_reproposes
                                          intro r hrange hante
                                          obtain ⟨_, m, hm, _⟩ := hante
                                          rw [hmp r hrange] at hm
                                          simp at hm
                                        · constructor
                                          · unfold all_past_start_round
                                            intro p hp r hrange
                                            rw [hr p hp]
                                            simp only [Finset.mem_Icc] at hrange
                                            omega
                                          · constructor
                                            · unfold all_rounds_below_have_precommit_quorum
                                              intro r hrange hlt
                                              have hfold :
                                                  List.foldl
                                                      (fun acc x => if x > acc then x else acc) 0
                                                      (Finset.toList
                                                        (Finset.image
                                                          (fun k => Finmap.lookupD k s.round)
                                                          (Finmap.keys s.round))) =
                                                    0 := by
                                                apply foldl_max_zero
                                                intro x hx
                                                rw [Finset.mem_toList] at hx
                                                rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
                                                rw [hkr] at hk
                                                exact hr k hk
                                              rw [hfold] at hlt
                                              simp only [Finset.mem_Icc] at hrange
                                              omega
                                            · constructor
                                              · unfold all_valid_in_current_round_precommitted
                                                intro p hp
                                                rw [hvr p hp, hr p hp]
                                                simp
                                              · constructor
                                                · unfold all_locked_round_below_valid_round
                                                  intro p hp
                                                  rw [hlr p hp, hvr p hp]
                                                · constructor
                                                  · unfold all_if_valid_round_then_precommitted
                                                    intro p hp
                                                    rw [hvr p hp]
                                                    simp
                                                  · unfold all_correct_proposal_valid_round_below_round
                                                    intro r hrange m hm _
                                                    rw [hmp r hrange] at hm
                                                    simp at hm

set_option maxHeartbeats 0 in
lemma insert_proposal_preserves_ind_type_ok {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (hstep : insert_proposal p s s') :
    ind_type_ok s' := by
  unfold insert_proposal at hstep
  rcases hstep with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hstepMap, hdecision, hlockedValue,
      hlockedRound, hvalidValue, hvalidRound, hprevote, hprecommit⟩
  rcases hact with
    ⟨_, _, _, _, v, hv, hproposals, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrange :
      Finmap.lookupD p s.round ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  have hvStored :
      Finmap.lookupD p s.valid_value ∈
        s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ := by
    have h := ht.valid_values p hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty,
      or_false] at h ⊢
    exact Or.elim h (fun hvv => Or.inl (Or.inl hvv))
      (fun hnil => Or.inr hnil)
  have hproposalValue :
      (if Finmap.lookupD p s.valid_value ≠ -1
        then Finmap.lookupD p s.valid_value else v) ∈
        s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ := by
    split
    · exact hvStored
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hproposalFacts :
      ProposalMapFacts s
        (Finmap.insert (Finmap.lookupD p s.round)
          (Finmap.lookupD (Finmap.lookupD p s.round) s.msgs_propose ∪
            insert
              (ProposalMsg.mk
                (if Finmap.lookupD p s.valid_value ≠ -1
                  then Finmap.lookupD p s.valid_value else v)
                (Finmap.lookupD p s.round) p
                (Finmap.lookupD p s.valid_round))
              ∅)
          s.msgs_propose) := by
    apply insert_proposal_map_facts ht.proposal_map_facts hrange
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      apply proposal_mk_mem_universe
      · exact Finset.mem_union.mpr (Or.inl hp)
      · exact hrange
      · exact hproposalValue
      · exact ht.valid_rounds p hp
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      rfl
  apply (ind_type_ok_iff_components s').mpr
  refine
    { round_keys := by simpa [hround, hCorr] using ht.round_keys
      round_values := by simpa [hround, hCorr, hMax] using ht.round_values
      step_keys := by simpa [hstepMap, hCorr] using ht.step_keys
      step_values := by simpa [hstepMap, hCorr] using ht.step_values
      decision_keys := by simpa [hdecision, hCorr] using ht.decision_keys
      decision_values := by
        simpa [hdecision, hCorr, hValid] using ht.decision_values
      locked_value_keys := by
        simpa [hlockedValue, hCorr] using ht.locked_value_keys
      locked_values := by
        simpa [hlockedValue, hCorr, hValid] using ht.locked_values
      locked_round_keys := by
        simpa [hlockedRound, hCorr] using ht.locked_round_keys
      locked_rounds := by
        simpa [hlockedRound, hCorr, hMax] using ht.locked_rounds
      valid_value_keys := by
        simpa [hvalidValue, hCorr] using ht.valid_value_keys
      valid_values := by
        simpa [hvalidValue, hCorr, hValid] using ht.valid_values
      valid_round_keys := by
        simpa [hvalidRound, hCorr] using ht.valid_round_keys
      valid_rounds := by
        simpa [hvalidRound, hCorr, hMax] using ht.valid_rounds
      proposal_keys := by
        simpa [hproposals, hMax] using hproposalFacts.keys
      proposals_typed := by
        simpa [hproposals, proposal_universe, hCorr, hFaulty, hValid,
          hInvalid, hMax]
          using hproposalFacts.typed
      proposals_round := by
        simpa [hproposals] using hproposalFacts.round
      prevote_keys := by
        simpa [hprevote, hMax] using ht.prevote_keys
      prevotes_typed := by
        simpa [hprevote, prevote_universe, hCorr, hFaulty, hValid,
          hInvalid, hMax]
          using ht.prevotes_typed
      prevotes_round := by
        simpa [hprevote] using ht.prevotes_round
      precommit_keys := by
        simpa [hprecommit, hMax] using ht.precommit_keys
      precommits_typed := by
        simpa [hprecommit, precommit_universe, hCorr, hFaulty, hValid,
          hInvalid, hMax]
          using ht.precommits_typed
      precommits_round := by
        simpa [hprecommit] using ht.precommits_round
      action_typed := by
        simp [haction, action_labels] }

lemma upon_proposal_in_propose_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_proposal_in_propose p s s') :
    ind_type_ok s' := by
  unfold upon_proposal_in_propose at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, hproposals, hprecommit⟩
  rcases hact with
    ⟨_, _, v, hv, _, hprevotes, hsteps, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  let r := Finmap.lookupD p s.round
  let voteValue :=
    if v ∈ s.ValidValues ∧
        (Finmap.lookupD p s.locked_round = -1 ∨
          Finmap.lookupD p s.locked_value = v)
      then v else -1
  have hrange : r ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  have hvote :
      voteValue ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ := by
    dsimp [voteValue]
    split
    · rename_i h
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl h.1)))
    · simp
  have hprevoteFacts :
      PrevoteMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_prevote ∪
            insert (VoteMsg.mk voteValue VoteKind.PREVOTE r p) ∅)
          s.msgs_prevote) := by
    apply insert_prevote_map_facts ht.prevote_map_facts hrange
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      exact prevote_mk_mem_universe
        (Finset.mem_union.mpr (Or.inl hp)) hrange hvote
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      rfl
  have hstepFacts :
      Finmap.keys (Finmap.insert p Step.PREVOTE s.step) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p Step.PREVOTE s.step) ∈
            insert Step.PROPOSE
              (insert Step.PREVOTE
                (insert Step.PRECOMMIT
                  (insert Step.DECIDED (∅ : Finset Step)))) := by
    apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
    simp
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using ht.round_keys
  · simpa [hround] using ht.round_values
  · simpa [hsteps] using hstepFacts.1
  · simpa [hsteps] using hstepFacts.2
  · simpa [hdecision] using ht.decision_keys
  · simpa [hdecision] using ht.decision_values
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using ht.proposal_map_facts
  · simpa [hprevotes, r, voteValue] using hprevoteFacts
  · simpa [hprecommit] using ht.precommit_map_facts
  · simp [haction, action_labels]

lemma add_prevote_preserves_ind_type_ok
    {s s' : State} {p r voteValue : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (hrange : r ∈ Finset.Icc 0 s.MaxRound)
    (hvote :
      voteValue ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hround : s'.round = s.round)
    (hsteps : s'.step = Finmap.insert p Step.PREVOTE s.step)
    (hdecision : s'.decision = s.decision)
    (hlockedValue : s'.locked_value = s.locked_value)
    (hlockedRound : s'.locked_round = s.locked_round)
    (hvalidValue : s'.valid_value = s.valid_value)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hproposals : s'.msgs_propose = s.msgs_propose)
    (hprevotes :
      s'.msgs_prevote =
        Finmap.insert r
          (Finmap.lookupD r s.msgs_prevote ∪
            insert (VoteMsg.mk voteValue VoteKind.PREVOTE r p) ∅)
          s.msgs_prevote)
    (hprecommit : s'.msgs_precommit = s.msgs_precommit)
    (haction : s'.last_action ∈ action_labels) :
    ind_type_ok s' := by
  have ht := (ind_type_ok_iff_components s).mp htype
  have hprevoteFacts :
      PrevoteMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_prevote ∪
            insert (VoteMsg.mk voteValue VoteKind.PREVOTE r p) ∅)
          s.msgs_prevote) := by
    apply insert_prevote_map_facts ht.prevote_map_facts hrange
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      exact prevote_mk_mem_universe
        (Finset.mem_union.mpr (Or.inl hp)) hrange hvote
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      rfl
  have hstepFacts :
      Finmap.keys (Finmap.insert p Step.PREVOTE s.step) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p Step.PREVOTE s.step) ∈
            insert Step.PROPOSE
              (insert Step.PREVOTE
                (insert Step.PRECOMMIT
                  (insert Step.DECIDED (∅ : Finset Step)))) := by
    apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
    simp
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using ht.round_keys
  · simpa [hround] using ht.round_values
  · simpa [hsteps] using hstepFacts.1
  · simpa [hsteps] using hstepFacts.2
  · simpa [hdecision] using ht.decision_keys
  · simpa [hdecision] using ht.decision_values
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using ht.proposal_map_facts
  · simpa [hprevotes] using hprevoteFacts
  · simpa [hprecommit] using ht.precommit_map_facts
  · exact haction

lemma add_precommit_preserves_ind_type_ok
    {s s' : State} {p r voteValue : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (hrange : r ∈ Finset.Icc 0 s.MaxRound)
    (hvote :
      voteValue ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hround : s'.round = s.round)
    (hsteps : s'.step = Finmap.insert p Step.PRECOMMIT s.step)
    (hdecision : s'.decision = s.decision)
    (hlockedValue : s'.locked_value = s.locked_value)
    (hlockedRound : s'.locked_round = s.locked_round)
    (hvalidValue : s'.valid_value = s.valid_value)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hproposals : s'.msgs_propose = s.msgs_propose)
    (hprevotes : s'.msgs_prevote = s.msgs_prevote)
    (hprecommit :
      s'.msgs_precommit =
        Finmap.insert r
          (Finmap.lookupD r s.msgs_precommit ∪
            insert (VoteMsg.mk voteValue VoteKind.PRECOMMIT r p) ∅)
          s.msgs_precommit)
    (haction : s'.last_action ∈ action_labels) :
    ind_type_ok s' := by
  have ht := (ind_type_ok_iff_components s).mp htype
  have hprecommitFacts :
      PrecommitMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_precommit ∪
            insert (VoteMsg.mk voteValue VoteKind.PRECOMMIT r p) ∅)
          s.msgs_precommit) := by
    apply insert_precommit_map_facts ht.precommit_map_facts hrange
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      exact precommit_mk_mem_universe
        (Finset.mem_union.mpr (Or.inl hp)) hrange hvote
    · intro m hm
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
      subst m
      rfl
  have hstepFacts :
      Finmap.keys (Finmap.insert p Step.PRECOMMIT s.step) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p Step.PRECOMMIT s.step) ∈
            insert Step.PROPOSE
              (insert Step.PREVOTE
                (insert Step.PRECOMMIT
                  (insert Step.DECIDED (∅ : Finset Step)))) := by
    apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
    simp
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using ht.round_keys
  · simpa [hround] using ht.round_values
  · simpa [hsteps] using hstepFacts.1
  · simpa [hsteps] using hstepFacts.2
  · simpa [hdecision] using ht.decision_keys
  · simpa [hdecision] using ht.decision_values
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using ht.proposal_map_facts
  · simpa [hprevotes] using ht.prevote_map_facts
  · simpa [hprecommit] using hprecommitFacts
  · exact haction

lemma upon_proposal_in_propose_and_prevote_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_proposal_in_propose_and_prevote p s s') :
    ind_type_ok s' := by
  unfold upon_proposal_in_propose_and_prevote at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, hproposals, hprecommit⟩
  rcases hact with
    ⟨_, _, v, hv, _, vr, hvr, _, _, _, _, hprevotes, hsteps, haction⟩
  let r := Finmap.lookupD p s.round
  let voteValue :=
    if v ∈ s.ValidValues ∧
        (Finmap.lookupD p s.locked_round ≤ vr ∨
          Finmap.lookupD p s.locked_value = v)
      then v else -1
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrange : r ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  have hvote :
      voteValue ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ := by
    dsimp [voteValue]
    split
    · rename_i h
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl h.1)))
    · simp
  exact add_prevote_preserves_ind_type_ok htype hp hrange hvote
    hCorr hFaulty hValid hInvalid hMax hround hsteps hdecision
    hlockedValue hlockedRound hvalidValue hvalidRound hproposals
    (by simpa [r, voteValue] using hprevotes) hprecommit
    (by simp [haction, action_labels])

lemma on_timeout_propose_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : on_timeout_propose p s s') :
    ind_type_ok s' := by
  unfold on_timeout_propose at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, hproposals, hprecommit⟩
  rcases hact with ⟨_, _, hprevotes, hsteps, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrange :
      Finmap.lookupD p s.round ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  exact add_prevote_preserves_ind_type_ok htype hp hrange (by simp)
    hCorr hFaulty hValid hInvalid hMax hround hsteps hdecision
    hlockedValue hlockedRound hvalidValue hvalidRound hproposals
    hprevotes hprecommit (by simp [haction, action_labels])

lemma upon_quorum_of_prevotes_any_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_quorum_of_prevotes_any p s s') :
    ind_type_ok s' := by
  unfold upon_quorum_of_prevotes_any at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, hproposals, hprevotes⟩
  rcases hact with
    ⟨_, _, evidence, _, _, hprecommit, hsteps, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrange :
      Finmap.lookupD p s.round ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  exact add_precommit_preserves_ind_type_ok htype hp hrange (by simp)
    hCorr hFaulty hValid hInvalid hMax hround hsteps hdecision
    hlockedValue hlockedRound hvalidValue hvalidRound hproposals
    hprevotes hprecommit (by simp [haction, action_labels])

lemma on_quorum_of_nil_prevotes_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : on_quorum_of_nil_prevotes p s s') :
    ind_type_ok s' := by
  unfold on_quorum_of_nil_prevotes at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, hproposals, hprevotes⟩
  rcases hact with ⟨_, _, hprecommit, hsteps, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrange :
      Finmap.lookupD p s.round ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  exact add_precommit_preserves_ind_type_ok htype hp hrange (by simp)
    hCorr hFaulty hValid hInvalid hMax hround hsteps hdecision
    hlockedValue hlockedRound hvalidValue hvalidRound hproposals
    hprevotes hprecommit (by simp [haction, action_labels])

lemma advance_round_preserves_ind_type_ok
    {s s' : State} {p newRound : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (hnewRound : newRound ∈ Finset.Icc 0 s.MaxRound)
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hround : s'.round = Finmap.insert p newRound s.round)
    (hsteps : s'.step = Finmap.insert p Step.PROPOSE s.step)
    (hdecision : s'.decision = s.decision)
    (hlockedValue : s'.locked_value = s.locked_value)
    (hlockedRound : s'.locked_round = s.locked_round)
    (hvalidValue : s'.valid_value = s.valid_value)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hproposals : s'.msgs_propose = s.msgs_propose)
    (hprevotes : s'.msgs_prevote = s.msgs_prevote)
    (hprecommit : s'.msgs_precommit = s.msgs_precommit)
    (haction : s'.last_action ∈ action_labels) :
    ind_type_ok s' := by
  have ht := (ind_type_ok_iff_components s).mp htype
  have hroundFacts :
      Finmap.keys (Finmap.insert p newRound s.round) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p newRound s.round) ∈
            Finset.Icc 0 s.MaxRound :=
    finmap_insert_preserves_values ht.round_keys ht.round_values hp hnewRound
  have hstepFacts :
      Finmap.keys (Finmap.insert p Step.PROPOSE s.step) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p Step.PROPOSE s.step) ∈
            insert Step.PROPOSE
              (insert Step.PREVOTE
                (insert Step.PRECOMMIT
                  (insert Step.DECIDED (∅ : Finset Step)))) := by
    apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
    simp
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using hroundFacts.1
  · simpa [hround] using hroundFacts.2
  · simpa [hsteps] using hstepFacts.1
  · simpa [hsteps] using hstepFacts.2
  · simpa [hdecision] using ht.decision_keys
  · simpa [hdecision] using ht.decision_values
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using ht.proposal_map_facts
  · simpa [hprevotes] using ht.prevote_map_facts
  · simpa [hprecommit] using ht.precommit_map_facts
  · exact haction

lemma decide_preserves_ind_type_ok
    {s s' : State} {p value : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (hvalue : value ∈ s.ValidValues)
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hround : s'.round = s.round)
    (hsteps : s'.step = Finmap.insert p Step.DECIDED s.step)
    (hdecision : s'.decision = Finmap.insert p value s.decision)
    (hlockedValue : s'.locked_value = s.locked_value)
    (hlockedRound : s'.locked_round = s.locked_round)
    (hvalidValue : s'.valid_value = s.valid_value)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hproposals : s'.msgs_propose = s.msgs_propose)
    (hprevotes : s'.msgs_prevote = s.msgs_prevote)
    (hprecommit : s'.msgs_precommit = s.msgs_precommit)
    (haction : s'.last_action ∈ action_labels) :
    ind_type_ok s' := by
  have ht := (ind_type_ok_iff_components s).mp htype
  have hdecisionFacts :
      Finmap.keys (Finmap.insert p value s.decision) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p value s.decision) ∈
            s.ValidValues ∪ insert (-1) ∅ := by
    apply finmap_insert_preserves_values
      ht.decision_keys ht.decision_values hp
    exact Finset.mem_union.mpr (Or.inl hvalue)
  have hstepFacts :
      Finmap.keys (Finmap.insert p Step.DECIDED s.step) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p Step.DECIDED s.step) ∈
            insert Step.PROPOSE
              (insert Step.PREVOTE
                (insert Step.PRECOMMIT
                  (insert Step.DECIDED (∅ : Finset Step)))) := by
    apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
    simp
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using ht.round_keys
  · simpa [hround] using ht.round_values
  · simpa [hsteps] using hstepFacts.1
  · simpa [hsteps] using hstepFacts.2
  · simpa [hdecision] using hdecisionFacts.1
  · simpa [hdecision] using hdecisionFacts.2
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using ht.proposal_map_facts
  · simpa [hprevotes] using ht.prevote_map_facts
  · simpa [hprecommit] using ht.precommit_map_facts
  · exact haction

lemma upon_quorum_of_precommits_any_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_quorum_of_precommits_any p s s') :
    ind_type_ok s' := by
  unfold upon_quorum_of_precommits_any at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hdecision, hlockedValue, hlockedRound, hvalidValue,
      hvalidRound, hproposals, hprevotes, hprecommit⟩
  rcases hact with
    ⟨_, evidence, _, _, hnextRound, _, hround, hsteps, haction⟩
  exact advance_round_preserves_ind_type_ok htype hp hnextRound
    hCorr hFaulty hValid hInvalid hMax hround hsteps hdecision
    hlockedValue hlockedRound hvalidValue hvalidRound hproposals
    hprevotes hprecommit (by simp [haction, action_labels])

lemma upon_proposal_in_precommit_no_decision_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_proposal_in_precommit_no_decision p s s') :
    ind_type_ok s' := by
  unfold upon_proposal_in_precommit_no_decision at ha
  rcases ha with
    ⟨_, _, hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hlockedValue, hlockedRound, hvalidValue,
      hvalidRound, hproposals, hprevotes, hprecommit⟩
  rcases hact with
    ⟨v, hv, _, rnd, hrnd, _, vr, hvr, _, _, hdecision, hsteps,
      haction⟩
  exact decide_preserves_ind_type_ok htype hp hv hCorr hFaulty
    hValid hInvalid hMax hround hsteps hdecision hlockedValue
    hlockedRound hvalidValue hvalidRound hproposals hprevotes
    hprecommit (by simp [haction, action_labels])

lemma on_round_catchup_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : on_round_catchup p s s') :
    ind_type_ok s' := by
  unfold on_round_catchup at ha
  rcases ha with
    ⟨_, hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hdecision, hlockedValue, hlockedRound, hvalidValue,
      hvalidRound, hproposals, hprevotes, hprecommit⟩
  rcases hact with
    ⟨rnd, hrnd, _, evPropose, _, _, evPrevote, _, _, evPrecommit, _,
      _, _, _, hround, hsteps, haction⟩
  exact advance_round_preserves_ind_type_ok htype hp hrnd hCorr
    hFaulty hValid hInvalid hMax hround hsteps hdecision hlockedValue
    hlockedRound hvalidValue hvalidRound hproposals hprevotes hprecommit
    (by simp [haction, action_labels])

lemma faulty_step_preserves_ind_type_ok {s s' : State}
    (htype : ind_type_ok s) (ha : faulty_step s s') :
    ind_type_ok s' := by
  unfold faulty_step at ha
  obtain
    ⟨_, hex, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hsteps, hdecision, hlockedValue, hlockedRound,
      hvalidValue, hvalidRound, haction⟩ := ha
  obtain ⟨r, hr, hrest⟩ := hex
  obtain ⟨_, hblock₁, _, hblock₂, _, hblock₃⟩ := hrest
  obtain
    ⟨fps₁, hfps₁, _, v₁, hv₁, _, vr₁, hvr₁, hproposals⟩ :=
    hblock₁
  obtain ⟨fps₂, hfps₂, _, v₂, hv₂, hprevotes⟩ := hblock₂
  obtain ⟨fps₃, hfps₃, _, v₃, hv₃, hprecommit⟩ := hblock₃
  have ht := (ind_type_ok_iff_components s).mp htype
  have hfps₁sub : fps₁ ⊆ s.Faulty := Finset.mem_powerset.mp hfps₁
  have hfps₂sub : fps₂ ⊆ s.Faulty := Finset.mem_powerset.mp hfps₂
  have hfps₃sub : fps₃ ⊆ s.Faulty := Finset.mem_powerset.mp hfps₃
  have hproposalFacts :
      ProposalMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_propose ∪
            Finset.image (fun src => ProposalMsg.mk v₁ r src vr₁) fps₁)
          s.msgs_propose) := by
    apply insert_proposal_map_facts ht.proposal_map_facts hr
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      apply proposal_mk_mem_universe
      · exact Finset.mem_union.mpr (Or.inr (hfps₁sub hsrc))
      · exact hr
      · exact Finset.mem_union.mpr
          (Or.inl hv₁)
      · exact hvr₁
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      rfl
  have hprevoteFacts :
      PrevoteMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_prevote ∪
            Finset.image
              (fun src => VoteMsg.mk v₂ VoteKind.PREVOTE r src) fps₂)
          s.msgs_prevote) := by
    apply insert_prevote_map_facts ht.prevote_map_facts hr
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      apply prevote_mk_mem_universe
      · exact Finset.mem_union.mpr (Or.inr (hfps₂sub hsrc))
      · exact hr
      · exact Finset.mem_union.mpr
          (Or.inl hv₂)
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      rfl
  have hprecommitFacts :
      PrecommitMapFacts s
        (Finmap.insert r
          (Finmap.lookupD r s.msgs_precommit ∪
            Finset.image
              (fun src => VoteMsg.mk v₃ VoteKind.PRECOMMIT r src) fps₃)
          s.msgs_precommit) := by
    apply insert_precommit_map_facts ht.precommit_map_facts hr
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      apply precommit_mk_mem_universe
      · exact Finset.mem_union.mpr (Or.inr (hfps₃sub hsrc))
      · exact hr
      · exact Finset.mem_union.mpr
          (Or.inl hv₃)
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨src, hsrc, rfl⟩
      rfl
  apply (ind_type_ok_iff_components s').mpr
  apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
  · simpa [hround] using ht.round_keys
  · simpa [hround] using ht.round_values
  · simpa [hsteps] using ht.step_keys
  · simpa [hsteps] using ht.step_values
  · simpa [hdecision] using ht.decision_keys
  · simpa [hdecision] using ht.decision_values
  · simpa [hlockedValue] using ht.locked_value_keys
  · simpa [hlockedValue] using ht.locked_values
  · simpa [hlockedRound] using ht.locked_round_keys
  · simpa [hlockedRound] using ht.locked_rounds
  · simpa [hvalidValue] using ht.valid_value_keys
  · simpa [hvalidValue] using ht.valid_values
  · simpa [hvalidRound] using ht.valid_round_keys
  · simpa [hvalidRound] using ht.valid_rounds
  · simpa [hproposals] using hproposalFacts
  · simpa [hprevotes] using hprevoteFacts
  · simpa [hprecommit] using hprecommitFacts
  · simpa [haction] using ht.action_typed

lemma upon_proposal_in_prevote_or_commit_and_prevote_preserves_ind_type_ok
    {s s' : State} {p : Int}
    (htype : ind_type_ok s) (hp : p ∈ s.Corr)
    (ha : upon_proposal_in_prevote_or_commit_and_prevote p s s') :
    ind_type_ok s' := by
  unfold upon_proposal_in_prevote_or_commit_and_prevote at ha
  rcases ha with
    ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
      hProposer, hround, hdecision, hproposals, hprevotes⟩
  rcases hact with
    ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, hvalidValue,
      hvalidRound, haction⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  let r := Finmap.lookupD p s.round
  have hrange : r ∈ Finset.Icc 0 s.MaxRound :=
    ht.round_values p hp
  have hvalidValueFacts :
      Finmap.keys (Finmap.insert p v s.valid_value) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p v s.valid_value) ∈
            s.ValidValues ∪ insert (-1) ∅ := by
    apply finmap_insert_preserves_values
      ht.valid_value_keys ht.valid_values hp
    exact Finset.mem_union.mpr (Or.inl hv)
  have hvalidRoundFacts :
      Finmap.keys (Finmap.insert p r s.valid_round) = s.Corr ∧
        ∀ q ∈ s.Corr,
          Finmap.lookupD q (Finmap.insert p r s.valid_round) ∈
            Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅ := by
    apply finmap_insert_preserves_values
      ht.valid_round_keys ht.valid_rounds hp
    exact Finset.mem_union.mpr (Or.inl hrange)
  rcases hbranch with hsend | hstay
  · rcases hsend with
      ⟨_, hlockedValue, hlockedRound, hprecommit, hsteps⟩
    have hstepFacts :
        Finmap.keys (Finmap.insert p Step.PRECOMMIT s.step) = s.Corr ∧
          ∀ q ∈ s.Corr,
            Finmap.lookupD q (Finmap.insert p Step.PRECOMMIT s.step) ∈
              insert Step.PROPOSE
                (insert Step.PREVOTE
                  (insert Step.PRECOMMIT
                    (insert Step.DECIDED (∅ : Finset Step)))) := by
      apply finmap_insert_preserves_values ht.step_keys ht.step_values hp
      simp
    have hlockedValueFacts :
        Finmap.keys (Finmap.insert p v s.locked_value) = s.Corr ∧
          ∀ q ∈ s.Corr,
            Finmap.lookupD q (Finmap.insert p v s.locked_value) ∈
              s.ValidValues ∪ insert (-1) ∅ := by
      apply finmap_insert_preserves_values
        ht.locked_value_keys ht.locked_values hp
      exact Finset.mem_union.mpr (Or.inl hv)
    have hlockedRoundFacts :
        Finmap.keys (Finmap.insert p r s.locked_round) = s.Corr ∧
          ∀ q ∈ s.Corr,
            Finmap.lookupD q (Finmap.insert p r s.locked_round) ∈
              Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅ := by
      apply finmap_insert_preserves_values
        ht.locked_round_keys ht.locked_rounds hp
      exact Finset.mem_union.mpr (Or.inl hrange)
    have hprecommitFacts :
        PrecommitMapFacts s
          (Finmap.insert r
            (Finmap.lookupD r s.msgs_precommit ∪
              insert (VoteMsg.mk v VoteKind.PRECOMMIT r p) ∅)
            s.msgs_precommit) := by
      apply insert_precommit_map_facts ht.precommit_map_facts hrange
      · intro m hm
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
        subst m
        apply precommit_mk_mem_universe
        · exact Finset.mem_union.mpr (Or.inl hp)
        · exact hrange
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
      · intro m hm
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hm
        subst m
        rfl
    apply (ind_type_ok_iff_components s').mpr
    apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
    · simpa [hround] using ht.round_keys
    · simpa [hround] using ht.round_values
    · simpa [hsteps] using hstepFacts.1
    · simpa [hsteps] using hstepFacts.2
    · simpa [hdecision] using ht.decision_keys
    · simpa [hdecision] using ht.decision_values
    · simpa [hlockedValue] using hlockedValueFacts.1
    · simpa [hlockedValue] using hlockedValueFacts.2
    · simpa [hlockedRound] using hlockedRoundFacts.1
    · simpa [hlockedRound] using hlockedRoundFacts.2
    · simpa [hvalidValue] using hvalidValueFacts.1
    · simpa [hvalidValue] using hvalidValueFacts.2
    · simpa [hvalidRound, r] using hvalidRoundFacts.1
    · simpa [hvalidRound, r] using hvalidRoundFacts.2
    · simpa [hproposals] using ht.proposal_map_facts
    · simpa [hprevotes] using ht.prevote_map_facts
    · simpa [hprecommit, r] using hprecommitFacts
    · simp [haction, action_labels]
  · rcases hstay with
      ⟨_, hlockedValue, hlockedRound, hprecommit, hsteps⟩
    apply (ind_type_ok_iff_components s').mpr
    apply type_components_of_updates hCorr hFaulty hValid hInvalid hMax
    · simpa [hround] using ht.round_keys
    · simpa [hround] using ht.round_values
    · simpa [hsteps] using ht.step_keys
    · simpa [hsteps] using ht.step_values
    · simpa [hdecision] using ht.decision_keys
    · simpa [hdecision] using ht.decision_values
    · simpa [hlockedValue] using ht.locked_value_keys
    · simpa [hlockedValue] using ht.locked_values
    · simpa [hlockedRound] using ht.locked_round_keys
    · simpa [hlockedRound] using ht.locked_rounds
    · simpa [hvalidValue] using hvalidValueFacts.1
    · simpa [hvalidValue] using hvalidValueFacts.2
    · simpa [hvalidRound, r] using hvalidRoundFacts.1
    · simpa [hvalidRound, r] using hvalidRoundFacts.2
    · simpa [hproposals] using ht.proposal_map_facts
    · simpa [hprevotes] using ht.prevote_map_facts
    · simpa [hprecommit] using ht.precommit_map_facts
    · simp [haction, action_labels]

theorem next_preserves_ind_type_ok {s s' : State}
    (htype : ind_type_ok s) (hnext : Next s s') :
    ind_type_ok s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · exact faulty_step_preserves_ind_type_ok htype hfaulty
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · exact insert_proposal_preserves_ind_type_ok htype hp h
    · exact upon_proposal_in_propose_preserves_ind_type_ok htype hp h
    · exact
        upon_proposal_in_propose_and_prevote_preserves_ind_type_ok
          htype hp h
    · exact upon_quorum_of_prevotes_any_preserves_ind_type_ok htype hp h
    · exact
        upon_proposal_in_prevote_or_commit_and_prevote_preserves_ind_type_ok
          htype hp h
    · exact upon_quorum_of_precommits_any_preserves_ind_type_ok htype hp h
    · exact
        upon_proposal_in_precommit_no_decision_preserves_ind_type_ok
          htype hp h
    · exact on_timeout_propose_preserves_ind_type_ok htype hp h
    · exact on_quorum_of_nil_prevotes_preserves_ind_type_ok htype hp h
    · exact on_round_catchup_preserves_ind_type_ok htype hp h

structure MessagesMonotone (s s' : State) : Prop where
  proposals : ∀ r,
    Finmap.lookupD r s.msgs_propose ⊆
      Finmap.lookupD r s'.msgs_propose
  prevotes : ∀ r,
    Finmap.lookupD r s.msgs_prevote ⊆
      Finmap.lookupD r s'.msgs_prevote
  precommits : ∀ r,
    Finmap.lookupD r s.msgs_precommit ⊆
      Finmap.lookupD r s'.msgs_precommit

lemma mem_lookupD_insert_union_iff {α β : Type}
    [DecidableEq α] [DecidableEq β] [Inhabited (Finset β)]
    {q r : α} {x : β} {fresh : Finset β}
    {fm : Finmap (fun _ : α => Finset β)} :
    x ∈ Finmap.lookupD q
        (Finmap.insert r (Finmap.lookupD r fm ∪ fresh) fm) ↔
      x ∈ Finmap.lookupD q fm ∨ q = r ∧ x ∈ fresh := by
  by_cases hqr : q = r
  · subst q
    simp only [lookupD_insert_self, Finset.mem_union]
    tauto
  · simp only [lookupD_insert_of_ne hqr, hqr, false_and, or_false]

lemma next_messages_monotone {s s' : State} (hnext : Next s s') :
    MessagesMonotone s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain
      ⟨_, hex, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
        hProposer, hround, hsteps, hdecision, hlockedValue, hlockedRound,
        hvalidValue, hvalidRound, haction⟩ := hfaulty
    obtain ⟨r, hr, hrest⟩ := hex
    obtain ⟨_, hblock₁, _, hblock₂, _, hblock₃⟩ := hrest
    obtain
      ⟨fps₁, hfps₁, _, v₁, hv₁, _, vr₁, hvr₁, hproposals⟩ :=
      hblock₁
    obtain ⟨fps₂, hfps₂, _, v₂, hv₂, hprevotes⟩ := hblock₂
    obtain ⟨fps₃, hfps₃, _, v₃, hv₃, hprecommit⟩ := hblock₃
    constructor
    · intro q
      simpa [hproposals] using
        (lookupD_subset_insert_union q r
          (Finset.image (fun src => ProposalMsg.mk v₁ r src vr₁) fps₁)
          s.msgs_propose)
    · intro q
      simpa [hprevotes] using
        (lookupD_subset_insert_union q r
          (Finset.image
            (fun src => VoteMsg.mk v₂ VoteKind.PREVOTE r src) fps₂)
          s.msgs_prevote)
    · intro q
      simpa [hprecommit] using
        (lookupD_subset_insert_union q r
          (Finset.image
            (fun src => VoteMsg.mk v₃ VoteKind.PRECOMMIT r src) fps₃)
          s.msgs_precommit)
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hprevotes,
          hprecommit⟩
      rcases hact with ⟨_, _, _, _, v, hv, hproposals, _⟩
      constructor
      · intro q
        simpa [hproposals] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (ProposalMsg.mk
                (if Finmap.lookupD p s.valid_value ≠ -1
                  then Finmap.lookupD p s.valid_value else v)
                (Finmap.lookupD p s.round) p
                (Finmap.lookupD p s.valid_round))
              ∅)
            s.msgs_propose)
      · simpa [hprevotes]
      · simpa [hprecommit]
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprecommit⟩
      rcases hact with
        ⟨_, _, v, hv, _, hprevotes, _, _⟩
      constructor
      · simpa [hproposals]
      · intro q
        simpa [hprevotes] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (VoteMsg.mk
                (if
                    v ∈ s.ValidValues ∧
                      (Finmap.lookupD p s.locked_round = -1 ∨
                        Finmap.lookupD p s.locked_value = v)
                  then v else -1)
                VoteKind.PREVOTE (Finmap.lookupD p s.round) p)
              ∅)
            s.msgs_prevote)
      · simpa [hprecommit]
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprecommit⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, _, _, hprevotes, _, _⟩
      constructor
      · simpa [hproposals]
      · intro q
        simpa [hprevotes] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (VoteMsg.mk
                (if
                    v ∈ s.ValidValues ∧
                      (Finmap.lookupD p s.locked_round ≤ vr ∨
                        Finmap.lookupD p s.locked_value = v)
                  then v else -1)
                VoteKind.PREVOTE (Finmap.lookupD p s.round) p)
              ∅)
            s.msgs_prevote)
      · simpa [hprecommit]
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes⟩
      rcases hact with
        ⟨_, _, evidence, _, _, hprecommit, _, _⟩
      constructor
      · simpa [hproposals]
      · simpa [hprevotes]
      · intro q
        simpa [hprecommit] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (VoteMsg.mk (-1) VoteKind.PRECOMMIT
                (Finmap.lookupD p s.round) p)
              ∅)
            s.msgs_precommit)
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, hproposals, hprevotes⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, _, _, _⟩
      constructor
      · simpa [hproposals]
      · simpa [hprevotes]
      · rcases hbranch with hsend | hstay
        · rcases hsend with ⟨_, _, _, hprecommit, _⟩
          intro q
          simpa [hprecommit] using
            (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
              (insert
                (VoteMsg.mk v VoteKind.PRECOMMIT
                  (Finmap.lookupD p s.round) p)
                ∅)
              s.msgs_precommit)
        · rcases hstay with ⟨_, _, _, hprecommit, _⟩
          simpa [hprecommit]
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes, hprecommit⟩
      exact ⟨by simpa [hproposals], by simpa [hprevotes],
        by simpa [hprecommit]⟩
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes, hprecommit⟩
      exact ⟨by simpa [hproposals], by simpa [hprevotes],
        by simpa [hprecommit]⟩
    · unfold on_timeout_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprecommit⟩
      rcases hact with ⟨_, _, hprevotes, _, _⟩
      constructor
      · simpa [hproposals]
      · intro q
        simpa [hprevotes] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (VoteMsg.mk (-1) VoteKind.PREVOTE
                (Finmap.lookupD p s.round) p)
              ∅)
            s.msgs_prevote)
      · simpa [hprecommit]
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes⟩
      rcases hact with ⟨_, _, hprecommit, _, _⟩
      constructor
      · simpa [hproposals]
      · simpa [hprevotes]
      · intro q
        simpa [hprecommit] using
          (lookupD_subset_insert_union q (Finmap.lookupD p s.round)
            (insert
              (VoteMsg.mk (-1) VoteKind.PRECOMMIT
                (Finmap.lookupD p s.round) p)
              ∅)
            s.msgs_precommit)
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes, hprecommit⟩
      exact ⟨by simpa [hproposals], by simpa [hprevotes],
        by simpa [hprecommit]⟩

/-- The facts about newly appended messages that are common to all protocol
transitions.  Faulty replicas may append arbitrary well-typed messages;
correct replicas append only at their current round and move to the
corresponding protocol step. -/
structure SourceEvolution (s s' : State) : Prop where
  round_mono : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.round ≤ Finmap.lookupD p s'.round
  proposals : ∀ r m, m ∈ Finmap.lookupD r s'.msgs_propose →
    m ∈ Finmap.lookupD r s.msgs_propose ∨
      m.src ∈ s.Faulty ∨
        m.src ∈ s.Corr ∧
          r = Finmap.lookupD m.src s.round ∧
            m.src = Finmap.lookupD r s.Proposer
  prevotes : ∀ r m, m ∈ Finmap.lookupD r s'.msgs_prevote →
    m ∈ Finmap.lookupD r s.msgs_prevote ∨
      m.src ∈ s.Faulty ∨
        m.src ∈ s.Corr ∧
          r = Finmap.lookupD m.src s.round ∧
            Finmap.lookupD m.src s'.step = Step.PREVOTE
  precommits : ∀ r m, m ∈ Finmap.lookupD r s'.msgs_precommit →
    m ∈ Finmap.lookupD r s.msgs_precommit ∨
      m.src ∈ s.Faulty ∨
        m.src ∈ s.Corr ∧
          r = Finmap.lookupD m.src s.round ∧
            Finmap.lookupD m.src s'.step = Step.PRECOMMIT

lemma next_source_evolution {s s' : State} (hnext : Next s s') :
    SourceEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain
      ⟨_, ⟨r, hr, _, ⟨fps₁, hfps₁, _, v₁, hv₁, _, vr₁, hvr₁,
        hproposals⟩, _, ⟨fps₂, hfps₂, _, v₂, hv₂, hprevotes⟩,
        _, fps₃, hfps₃, _, v₃, hv₃, hprecommits⟩,
        _, _, _, _, _, _, _, _, hround, _, _⟩ := hfaulty
    constructor
    · intro q hq
      simp [hround]
    · intro q m hm
      rw [hproposals, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact Or.inl hm
      · right; left
        simp only [Finset.mem_image] at hm
        rcases hm with ⟨src, hsrc, rfl⟩
        exact Finset.mem_powerset.mp hfps₁ hsrc
    · intro q m hm
      rw [hprevotes, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact Or.inl hm
      · right; left
        simp only [Finset.mem_image] at hm
        rcases hm with ⟨src, hsrc, rfl⟩
        exact Finset.mem_powerset.mp hfps₂ hsrc
    · intro q m hm
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact Or.inl hm
      · right; left
        simp only [Finset.mem_image] at hm
        rcases hm with ⟨src, hsrc, rfl⟩
        exact Finset.mem_powerset.mp hfps₃ hsrc
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, hstep, _, _, _, _, _,
          hprevotes, hprecommits⟩
      rcases hact with
        ⟨hproposer, _, _, _, v, hv, hproposals, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        rw [hproposals, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simpa [hqr] using hproposer⟩
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with ⟨_, _, v, hv, _, hprevotes, hstep, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        rw [hprevotes, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simp [hstep]⟩
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, _, _, hprevotes, hstep, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        rw [hprevotes, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simp [hstep]⟩
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _,
          hproposals, hprevotes⟩
      rcases hact with
        ⟨_, _, evidence, _, _, hprecommits, hstep, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        rw [hprecommits, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simp [hstep]⟩
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, hproposals,
          hprevotes⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, _, _, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        rcases hbranch with hsend | hstay
        · rcases hsend with ⟨_, _, _, hprecommits, hstep⟩
          rw [hprecommits, mem_lookupD_insert_union_iff] at hm
          rcases hm with hm | ⟨hqr, hm⟩
          · exact Or.inl hm
          · right; right
            simp at hm
            subst m
            exact ⟨hp, hqr, by simp [hstep]⟩
        · rcases hstay with ⟨_, _, _, hprecommits, _⟩
          exact Or.inl (by simpa [hprecommits] using hm)
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprevotes, hprecommits⟩
      rcases hact with
        ⟨_, evidence, _, hcard, hrange, _, hround, hstep, _⟩
      constructor
      · intro q hq
        by_cases hqp : q = p
        · subst q; rw [hround, lookupD_insert_self]; omega
        · rw [hround, lookupD_insert_of_ne hqp]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, hact, _, _, _, _, _, _, _, _, hround, _, _, _, _,
          hproposals, hprevotes, hprecommits⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold on_timeout_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with ⟨_, _, hprevotes, hstep, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        rw [hprevotes, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simp [hstep]⟩
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _,
          hproposals, hprevotes⟩
      rcases hact with ⟨_, _, hprecommits, hstep, _⟩
      constructor
      · intro q hq; simp [hround]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        rw [hprecommits, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hqr, hm⟩
        · exact Or.inl hm
        · right; right
          simp at hm
          subst m
          exact ⟨hp, hqr, by simp [hstep]⟩
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, hact, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprevotes, hprecommits⟩
      rcases hact with
        ⟨rnd, hrnd, _, _, _, _, _, _, _, _, _, hgt, _, _, hround,
          hstep, _⟩
      constructor
      · intro q hq
        by_cases hqp : q = p
        · subst q; rw [hround, lookupD_insert_self]; omega
        · rw [hround, lookupD_insert_of_ne hqp]
      · intro q m hm
        exact Or.inl (by simpa [hproposals] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprevotes] using hm)
      · intro q m hm
        exact Or.inl (by simpa [hprecommits] using hm)

inductive DecisionEvolution (s s' : State) : Prop where
  | frame (hdecision : s'.decision = s.decision)
  | decide (p value round validRound : Int)
      (hp : p ∈ s.Corr) (hvalue : value ∈ s.ValidValues)
      (hround : round ∈ Finset.Icc 0 s.MaxRound)
      (hvalidRound :
        validRound ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅)
      (hproposal :
        ProposalMsg.mk value round (Finmap.lookupD round s.Proposer)
          validRound ∈ Finmap.lookupD round s.msgs_propose)
      (hquorum :
        (Finset.filter (fun m => value = m.id)
          (Finmap.lookupD round s.msgs_precommit)).card ≥ 2 * s.T + 1)
      (hdecision :
        s'.decision = Finmap.insert p value s.decision)
      (hstep : s'.step = Finmap.insert p Step.DECIDED s.step)

lemma next_decision_evolution {s s' : State} (hnext : Next s s') :
    DecisionEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecision, _⟩
    exact .frame hdecision
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨value, hvalue, _, round, hround, _, validRound, hvalidRound,
          hproposal, hquorum, hdecision, hstep, _⟩
      exact .decide p value round validRound hp hvalue hround hvalidRound
        hproposal hquorum hdecision hstep
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hdecision, _⟩
      exact .frame hdecision

inductive ValidEvolution (s s' : State) : Prop where
  | frame
      (hvalidValue : s'.valid_value = s.valid_value)
      (hvalidRound : s'.valid_round = s.valid_round)
  | update (p value : Int)
      (hp : p ∈ s.Corr) (hvalue : value ∈ s.ValidValues)
      (hvalidValue :
        s'.valid_value = Finmap.insert p value s.valid_value)
      (hvalidRound :
        s'.valid_round =
          Finmap.insert p (Finmap.lookupD p s.round) s.valid_round)
      (hquorum :
        (Finset.filter (fun m => value = m.id)
          (Finmap.lookupD (Finmap.lookupD p s.round)
            s.msgs_prevote)).card ≥ 2 * s.T + 1)
      (hstep : Finmap.lookupD p s'.step = Step.PRECOMMIT)
      (hsent :
        (∃ m ∈ Finmap.lookupD (Finmap.lookupD p s.round)
              s'.msgs_precommit,
            p = m.src ∧ m.id = value) ∨
          (Finmap.lookupD p s.step = Step.PRECOMMIT ∧
            s'.msgs_precommit = s.msgs_precommit))

lemma next_valid_evolution {s s' : State} (hnext : Next s s') :
    ValidEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalidValue,
        hvalidRound, _⟩
    exact .frame hvalidValue hvalidRound
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, hround, _, _, _⟩
      rcases hact with
        ⟨hstepOld, _, value, hvalue, _, vr, hvr, _, hquorum,
          hbranch, hvalidValue, hvalidRound, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with
          ⟨_, _, _, hprecommits, hstep⟩
        apply ValidEvolution.update p value hp hvalue hvalidValue
          hvalidRound hquorum
        · simp [hstep]
        · left
          refine ⟨VoteMsg.mk value VoteKind.PRECOMMIT
            (Finmap.lookupD p s.round) p, ?_, rfl, rfl⟩
          rw [hprecommits, lookupD_insert_self]
          simp
      · rcases hstay with
          ⟨hnotPrevote, _, _, hprecommits, hstep⟩
        have hprecommitOld :
            Finmap.lookupD p s.step = Step.PRECOMMIT := by
          rcases hstepOld with hs | hs
          · exact (hnotPrevote hs).elim
          · exact hs
        apply ValidEvolution.update p value hp hvalue hvalidValue
          hvalidRound hquorum
        · simpa [hstep] using hprecommitOld
        · exact Or.inr ⟨hprecommitOld, hprecommits⟩
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _⟩
      exact .frame hvalidValue hvalidRound
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _, _, _⟩
      exact .frame hvalidValue hvalidRound

inductive LockedEvolution (s s' : State) : Prop where
  | frame
      (hlockedValue : s'.locked_value = s.locked_value)
      (hlockedRound : s'.locked_round = s.locked_round)
  | update (p value : Int)
      (hp : p ∈ s.Corr) (hvalue : value ∈ s.ValidValues)
      (hlockedValue :
        s'.locked_value = Finmap.insert p value s.locked_value)
      (hlockedRound :
        s'.locked_round =
          Finmap.insert p (Finmap.lookupD p s.round) s.locked_round)
      (hvalidRound :
        s'.valid_round =
          Finmap.insert p (Finmap.lookupD p s.round) s.valid_round)
      (hsent : VoteMsg.mk value VoteKind.PRECOMMIT
          (Finmap.lookupD p s.round) p ∈
        Finmap.lookupD (Finmap.lookupD p s.round) s'.msgs_precommit)

lemma next_locked_evolution {s s' : State} (hnext : Next s s') :
    LockedEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlockedValue,
        hlockedRound, _⟩
    exact .frame hlockedValue hlockedRound
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, _, value, hvalue, _, _, _, _, _, hbranch, _, hvalidRound, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with
          ⟨_, hlockedValue, hlockedRound, hprecommits, _⟩
        apply LockedEvolution.update p value hp hvalue
          hlockedValue hlockedRound hvalidRound
        rw [hprecommits, lookupD_insert_self]
        simp
      · rcases hstay with
          ⟨_, hlockedValue, hlockedRound, _, _⟩
        exact .frame hlockedValue hlockedRound
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold on_timeout_propose at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact .frame hlockedValue hlockedRound

def PrevoteWitness (s : State) (p : Int) : Prop :=
  ∃ m ∈ Finmap.lookupD (Finmap.lookupD p s.round) s.msgs_prevote,
    m.id ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ ∧ p = m.src

def PrecommitWitness (s : State) (p : Int) : Prop :=
  ∃ m ∈ Finmap.lookupD (Finmap.lookupD p s.round) s.msgs_precommit,
    m.id ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅ ∧ p = m.src

inductive StepEvolution (s s' : State) : Prop where
  | frame (hstep : s'.step = s.step) (hround : s'.round = s.round)
  | update (p : Int) (hp : p ∈ s.Corr) (newStep : Step)
      (hstep : s'.step = Finmap.insert p newStep s.step)
      (hroundOther : ∀ q, q ≠ p →
        Finmap.lookupD q s'.round = Finmap.lookupD q s.round)
      (hprevoteOld : newStep = Step.PREVOTE →
        Finmap.lookupD p s.step = Step.PROPOSE)
      (hproposeAdvance : newStep = Step.PROPOSE →
        Finmap.lookupD p s.round < Finmap.lookupD p s'.round)
      (hprevote : newStep = Step.PREVOTE → PrevoteWitness s' p)
      (hprecommit : newStep = Step.PRECOMMIT → PrecommitWitness s' p)

lemma next_step_evolution {s s' : State} (hnext : Next s s') :
    StepEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with ⟨_, _, _, _, _, _, _, _, _, _, hround, hstep, _⟩
    exact .frame hstep hround
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, hstep, _⟩
      exact .frame hstep hround
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _, _,
          _, _, _⟩
      rcases hact with
        ⟨hstepOld, _, v, hv, _, hprevotes, hstep, _⟩
      refine StepEvolution.update p hp Step.PREVOTE hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro _
        exact hstepOld
      · intro h
        contradiction
      · intro _
        unfold PrevoteWitness
        let voteValue :=
          if v ∈ s.ValidValues ∧
              (Finmap.lookupD p s.locked_round = -1 ∨
                Finmap.lookupD p s.locked_value = v)
            then v else -1
        refine ⟨VoteMsg.mk voteValue VoteKind.PREVOTE
          (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
        · rw [hprevotes, hround, lookupD_insert_self]
          simp [voteValue]
        · rw [hValid, hInvalid]
          dsimp [voteValue]
          split
          · rename_i hvcond
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl hvcond.1)))
          · simp
      · intro h
        contradiction
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _, _,
          _, _, _⟩
      rcases hact with
        ⟨hstepOld, _, v, hv, _, vr, hvr, _, _, _, _, hprevotes, hstep, _⟩
      refine StepEvolution.update p hp Step.PREVOTE hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro _
        exact hstepOld
      · intro h
        contradiction
      · intro _
        unfold PrevoteWitness
        let voteValue :=
          if v ∈ s.ValidValues ∧
              (Finmap.lookupD p s.locked_round ≤ vr ∨
                Finmap.lookupD p s.locked_value = v)
            then v else -1
        refine ⟨VoteMsg.mk voteValue VoteKind.PREVOTE
          (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
        · rw [hprevotes, hround, lookupD_insert_self]
          simp [voteValue]
        · rw [hValid, hInvalid]
          dsimp [voteValue]
          split
          · rename_i hvcond
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl hvcond.1)))
          · simp
      · intro h
        contradiction
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _, _,
          _, _⟩
      rcases hact with
        ⟨_, _, evidence, _, _, hprecommit, hstep, _⟩
      refine StepEvolution.update p hp Step.PRECOMMIT hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro h
        contradiction
      · intro h
        contradiction
      · intro h
        contradiction
      · intro _
        unfold PrecommitWitness
        refine ⟨VoteMsg.mk (-1) VoteKind.PRECOMMIT
          (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
        · rw [hprecommit, hround, lookupD_insert_self]
          simp
        · rw [hValid, hInvalid]
          simp
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with ⟨_, _, _, hprecommit, hstep⟩
        refine StepEvolution.update p hp Step.PRECOMMIT hstep ?_ ?_ ?_ ?_ ?_
        · intro q hqp
          simp [hround]
        · intro h
          contradiction
        · intro h
          contradiction
        · intro h
          contradiction
        · intro _
          unfold PrecommitWitness
          refine ⟨VoteMsg.mk v VoteKind.PRECOMMIT
            (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
          · rw [hprecommit, hround, lookupD_insert_self]
            simp
          · rw [hValid, hInvalid]
            exact Finset.mem_union.mpr
              (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
      · rcases hstay with ⟨_, _, _, _, hstep⟩
        exact .frame hstep hround
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, _, _, _, _, _, hround, hstep, _⟩
      refine StepEvolution.update p hp Step.PROPOSE hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        rw [hround, lookupD_insert_of_ne hqp]
      · intro h
        contradiction
      · intro _
        rw [hround, lookupD_insert_self]
        omega
      · intro h
        contradiction
      · intro h
        contradiction
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, hact, _, _, _, _, _, _, _, _, hround, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨v, hv, _, rnd, hrnd, _, vr, hvr, _, _, _, hstep, _⟩
      refine StepEvolution.update p hp Step.DECIDED hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro h
        contradiction
      · intro h
        contradiction
      · intro h
        contradiction
      · intro h
        contradiction
    · unfold on_timeout_propose at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _, _,
          _, _, _⟩
      rcases hact with ⟨hstepOld, _, hprevotes, hstep, _⟩
      refine StepEvolution.update p hp Step.PREVOTE hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro _
        exact hstepOld
      · intro h
        contradiction
      · intro _
        unfold PrevoteWitness
        refine ⟨VoteMsg.mk (-1) VoteKind.PREVOTE
          (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
        · rw [hprevotes, hround, lookupD_insert_self]
          simp
        · rw [hValid, hInvalid]
          simp
      · intro h
        contradiction
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, hValid, hInvalid, _, _, hround, _, _, _, _,
          _, _⟩
      rcases hact with ⟨_, _, hprecommit, hstep, _⟩
      refine StepEvolution.update p hp Step.PRECOMMIT hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        simp [hround]
      · intro h
        contradiction
      · intro h
        contradiction
      · intro h
        contradiction
      · intro _
        unfold PrecommitWitness
        refine ⟨VoteMsg.mk (-1) VoteKind.PRECOMMIT
          (Finmap.lookupD p s.round) p, ?_, ?_, rfl⟩
        · rw [hprecommit, hround, lookupD_insert_self]
          simp
        · rw [hValid, hInvalid]
          simp
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨rnd, hrnd, _, _, _, _, _, _, _, _, _, _, _, _, hround,
          hstep, _⟩
      refine StepEvolution.update p hp Step.PROPOSE hstep ?_ ?_ ?_ ?_ ?_
      · intro q hqp
        rw [hround, lookupD_insert_of_ne hqp]
      · intro h
        contradiction
      · intro _
        rw [hround, lookupD_insert_self]
        omega
      · intro h
        contradiction
      · intro h
        contradiction

lemma next_step_progress_same_round {s s' : State}
    (hnext : Next s s') {q : Int}
    (hr : Finmap.lookupD q s'.round = Finmap.lookupD q s.round) :
    ((Finmap.lookupD q s.step = Step.PREVOTE ∨
        Finmap.lookupD q s.step = Step.PRECOMMIT ∨
          Finmap.lookupD q s.step = Step.DECIDED) →
      (Finmap.lookupD q s'.step = Step.PREVOTE ∨
        Finmap.lookupD q s'.step = Step.PRECOMMIT ∨
          Finmap.lookupD q s'.step = Step.DECIDED)) ∧
    ((Finmap.lookupD q s.step = Step.PRECOMMIT ∨
        Finmap.lookupD q s.step = Step.DECIDED) →
      (Finmap.lookupD q s'.step = Step.PRECOMMIT ∨
        Finmap.lookupD q s'.step = Step.DECIDED)) := by
  rcases next_step_evolution hnext with ⟨hstep, hround⟩ |
    ⟨p, hp, newStep, hstep, hroundOther, hprevoteOld,
      hproposeAdvance, hprevote, hprecommit⟩
  · simpa [hstep]
  · by_cases hqp : q = p
    · subst q
      have hlookup :
          Finmap.lookupD p s'.step = newStep := by simp [hstep]
      constructor
      · intro hold
        cases newStep with
        | PROPOSE =>
            have := hproposeAdvance rfl
            omega
        | PREVOTE => exact Or.inl hlookup
        | PRECOMMIT => exact Or.inr (Or.inl hlookup)
        | DECIDED => exact Or.inr (Or.inr hlookup)
      · intro hold
        cases newStep with
        | PROPOSE =>
            have := hproposeAdvance rfl
            omega
        | PREVOTE =>
            have hOldPropose := hprevoteOld rfl
            rcases hold with hold | hold <;> simp_all
        | PRECOMMIT => exact Or.inl hlookup
        | DECIDED => exact Or.inr hlookup
    · have hlookup :
          Finmap.lookupD q s'.step = Finmap.lookupD q s.step := by
        simp [hstep, lookupD_insert_of_ne hqp]
      simpa [hlookup]

lemma prevote_witness_transfer {s s' : State} {p : Int}
    (hw : PrevoteWitness s p)
    (hmono : MessagesMonotone s s')
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hround :
      Finmap.lookupD p s'.round = Finmap.lookupD p s.round) :
    PrevoteWitness s' p := by
  rcases hw with ⟨m, hm, hid, hsrc⟩
  refine ⟨m, ?_, ?_, hsrc⟩
  · rw [hround]
    exact hmono.prevotes _ hm
  · simpa [hValid, hInvalid] using hid

lemma precommit_witness_transfer {s s' : State} {p : Int}
    (hw : PrecommitWitness s p)
    (hmono : MessagesMonotone s s')
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hround :
      Finmap.lookupD p s'.round = Finmap.lookupD p s.round) :
    PrecommitWitness s' p := by
  rcases hw with ⟨m, hm, hid, hsrc⟩
  refine ⟨m, ?_, ?_, hsrc⟩
  · rw [hround]
    exact hmono.precommits _ hm
  · simpa [hValid, hInvalid] using hid

lemma correct_precommit_round_le_current {s : State}
    (hnofuture : all_no_future_messages_sent s)
    {p r : Int} (hp : p ∈ s.Corr)
    (hr : r ∈ Finset.Icc 0 s.MaxRound)
    {m : VoteMsg} (hm : m ∈ Finmap.lookupD r s.msgs_precommit)
    (hsrc : p = m.src) :
    r ≤ Finmap.lookupD p s.round := by
  by_contra hnot
  have hgt : r > Finmap.lookupD p s.round := by omega
  have hrFuture :
      r ∈ Finset.filter
        (fun x => x > Finmap.lookupD p s.round)
        (Finset.Icc 0 s.MaxRound) :=
    Finset.mem_filter.mpr ⟨hr, hgt⟩
  have hne := (hnofuture p hp).2 r hrFuture |>.2.2 m hm
  exact hne hsrc

/-- A non-nil precommit newly introduced by a correct transition is exactly
the precommit that installs the sender's post-state lock.  Faulty transitions
can only introduce messages whose source is faulty. -/
lemma next_fresh_nonnil_precommit_lock {s s' : State}
    (hnext : Next s s') {r : Int} {m : VoteMsg}
    (hm : m ∈ Finmap.lookupD r s'.msgs_precommit)
    (hmOld : m ∉ Finmap.lookupD r s.msgs_precommit)
    (hnil : m.id ≠ -1) :
    m.src ∈ s.Faulty ∨
      m.src ∈ s.Corr ∧
        Finmap.lookupD m.src s'.locked_round = r ∧
          Finmap.lookupD m.src s'.locked_value = m.id := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, _, _, _, _, hblock⟩ := hrest
    obtain ⟨fps, hfps, _, value, _, hprecommits⟩ := hblock
    rw [hprecommits, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact (hmOld hm).elim
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrc, rfl⟩
      exact Or.inl (Finset.mem_powerset.mp hfps hsrc)
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _⟩
      rcases hact with ⟨_, _, _, _, _, hprecommits, _, _⟩
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact (hmOld hm).elim
      · simp at hm
        subst m
        exact (hnil rfl).elim
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, _, value, _, _, _, _, _, _, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with
          ⟨_, hlockedValue, hlockedRound, hprecommits, _⟩
        rw [hprecommits, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hrEq, hm⟩
        · exact (hmOld hm).elim
        · simp at hm
          subst m
          right
          refine ⟨hp, ?_, ?_⟩
          · simp [hlockedRound, hrEq]
          · simp [hlockedValue]
      · rcases hstay with ⟨_, _, _, hprecommits, _⟩
        exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _⟩
      rcases hact with ⟨_, _, hprecommits, _, _⟩
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact (hmOld hm).elim
      · simp at hm
        subst m
        exact (hnil rfl).elim
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim

lemma next_preserves_prevote_sent {s s' : State}
    (hold : all_if_in_prevote_then_sent_prevote s)
    (hnext : Next s s') :
    all_if_in_prevote_then_sent_prevote s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, hValid, hInvalid, _, _⟩
  unfold all_if_in_prevote_then_sent_prevote at hold ⊢
  intro q hq hstepq
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_step_evolution hnext with ⟨hstep, hround⟩ |
    ⟨p, hp, newStep, hstep, hroundOther, hprevoteOld,
      hproposeAdvance, hprevote, hprecommit⟩
  · apply prevote_witness_transfer (hold q hqOld (by simpa [hstep] using hstepq))
      hmono hValid hInvalid
    simp [hround]
  · by_cases hqp : q = p
    · subst q
      have hnew : newStep = Step.PREVOTE := by
        simpa [hstep] using hstepq
      exact hprevote hnew
    · have hstepOld : Finmap.lookupD q s.step = Step.PREVOTE := by
        simpa [hstep, lookupD_insert_of_ne hqp] using hstepq
      exact prevote_witness_transfer (hold q hqOld hstepOld)
        hmono hValid hInvalid (hroundOther q hqp)

lemma next_preserves_precommit_sent {s s' : State}
    (hold : all_if_in_precommit_then_sent_precommit s)
    (hnext : Next s s') :
    all_if_in_precommit_then_sent_precommit s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, hValid, hInvalid, _, _⟩
  unfold all_if_in_precommit_then_sent_precommit at hold ⊢
  intro q hq hstepq
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_step_evolution hnext with ⟨hstep, hround⟩ |
    ⟨p, hp, newStep, hstep, hroundOther, hprevoteOld,
      hproposeAdvance, hprevote, hprecommit⟩
  · apply precommit_witness_transfer
      (hold q hqOld (by simpa [hstep] using hstepq))
      hmono hValid hInvalid
    simp [hround]
  · by_cases hqp : q = p
    · subst q
      have hnew : newStep = Step.PRECOMMIT := by
        simpa [hstep] using hstepq
      exact hprecommit hnew
    · have hstepOld : Finmap.lookupD q s.step = Step.PRECOMMIT := by
        simpa [hstep, lookupD_insert_of_ne hqp] using hstepq
      exact precommit_witness_transfer (hold q hqOld hstepOld)
        hmono hValid hInvalid (hroundOther q hqp)

lemma decided_valid_frame {s s' : State}
    (hinv : all_if_in_decided_then_valid_decision s)
    (hCorr : s'.Corr = s.Corr)
    (hValid : s'.ValidValues = s.ValidValues)
    (hstep : s'.step = s.step)
    (hdecision : s'.decision = s.decision) :
    all_if_in_decided_then_valid_decision s' := by
  unfold all_if_in_decided_then_valid_decision at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  simpa [hCorr, hValid, hstep, hdecision] using hinv q hq

lemma decided_valid_step_update {s s' : State} {p : Int} {newStep : Step}
    (hinv : all_if_in_decided_then_valid_decision s)
    (hp : p ∈ s.Corr)
    (hold : Finmap.lookupD p s.step ≠ Step.DECIDED)
    (hnew : newStep ≠ Step.DECIDED)
    (hCorr : s'.Corr = s.Corr)
    (hValid : s'.ValidValues = s.ValidValues)
    (hstep : s'.step = Finmap.insert p newStep s.step)
    (hdecision : s'.decision = s.decision) :
    all_if_in_decided_then_valid_decision s' := by
  unfold all_if_in_decided_then_valid_decision at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  rw [hValid, hstep, hdecision]
  by_cases hqp : q = p
  · subst q
    simp only [lookupD_insert_self]
    apply propext
    constructor
    · exact fun h => (hnew h).elim
    · intro hvalid
      exact (hold ((hinv p hp).mpr hvalid)).elim
  · rw [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma decided_valid_decide {s s' : State} {p value : Int}
    (hinv : all_if_in_decided_then_valid_decision s)
    (hp : p ∈ s.Corr) (hvalue : value ∈ s.ValidValues)
    (hCorr : s'.Corr = s.Corr)
    (hValid : s'.ValidValues = s.ValidValues)
    (hstep : s'.step = Finmap.insert p Step.DECIDED s.step)
    (hdecision : s'.decision = Finmap.insert p value s.decision) :
    all_if_in_decided_then_valid_decision s' := by
  unfold all_if_in_decided_then_valid_decision at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  rw [hValid, hstep, hdecision]
  by_cases hqp : q = p
  · subst q
    simp [hvalue]
  · simp only [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma next_preserves_decided_valid {s s' : State}
    (hinv : all_if_in_decided_then_valid_decision s)
    (hnext : Next s s') :
    all_if_in_decided_then_valid_decision s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, hCorr, _, _, _, hValid, _, _, _, _, hstep, hdecision, _⟩
    exact decided_valid_frame hinv hCorr hValid hstep hdecision
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨_, hCorr, _, _, _, hValid, _, _, _, _, hstep, hdecision, _⟩
      exact decided_valid_frame hinv hCorr hValid hstep hdecision
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with ⟨hold, _, _, _, _, _, hstep, _⟩
      exact decided_valid_step_update hinv hp (by simp [hold])
        (by decide) hCorr hValid hstep hdecision
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with
        ⟨hold, _, _, _, _, _, _, _, _, _, _, _, hstep, _⟩
      exact decided_valid_step_update hinv hp (by simp [hold])
        (by decide) hCorr hValid hstep hdecision
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with ⟨hold, _, _, _, _, _, hstep, _⟩
      exact decided_valid_step_update hinv hp (by simp [hold])
        (by decide) hCorr hValid hstep hdecision
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with
        ⟨_, _, _, _, _, _, _, _, _, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with ⟨hold, _, _, _, hstep⟩
        exact decided_valid_step_update hinv hp (by simp [hold])
          (by decide) hCorr hValid hstep hdecision
      · rcases hstay with ⟨_, _, _, _, hstep⟩
        exact decided_valid_frame hinv hCorr hValid hstep hdecision
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, _, _, _, _, hold, _, hstep, _⟩
      exact decided_valid_step_update hinv hp hold (by decide)
        hCorr hValid hstep (by aesop)
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, hact, hCorr, _, _, _, hValid, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨value, hvalue, _, _, _, _, _, _, _, _, hdecision, hstep, _⟩
      exact decided_valid_decide hinv hp hvalue hCorr hValid hstep hdecision
    · unfold on_timeout_propose at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with ⟨hold, _, _, hstep, _⟩
      exact decided_valid_step_update hinv hp (by simp [hold])
        (by decide) hCorr hValid hstep hdecision
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, hCorr, _, _, _, hValid, _, _, _, _, hdecision, _⟩
      rcases hact with ⟨hold, _, _, hstep, _⟩
      exact decided_valid_step_update hinv hp (by simp [hold])
        (by decide) hCorr hValid hstep hdecision
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, hact, hCorr, _, _, _, hValid, _, _, _, hdecision, _⟩
      rcases hact with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hold, _, hstep, _⟩
      exact decided_valid_step_update hinv hp hold (by decide)
        hCorr hValid hstep hdecision

lemma nil_iff_maps_frame {s s' : State}
    {left right : State → Finmap (fun _ : Int => Int)}
    (hinv : ∀ p ∈ s.Corr,
      (Finmap.lookupD p (left s) = -1) =
        (Finmap.lookupD p (right s) = -1))
    (hCorr : s'.Corr = s.Corr)
    (hleft : left s' = left s) (hright : right s' = right s) :
    ∀ p ∈ s'.Corr,
      (Finmap.lookupD p (left s') = -1) =
        (Finmap.lookupD p (right s') = -1) := by
  intro p hp
  rw [hCorr] at hp
  simpa [hleft, hright] using hinv p hp

lemma nil_iff_maps_insert {s s' : State}
    {left right : State → Finmap (fun _ : Int => Int)}
    (hinv : ∀ p ∈ s.Corr,
      (Finmap.lookupD p (left s) = -1) =
        (Finmap.lookupD p (right s) = -1))
    {p leftValue rightValue : Int} (hp : p ∈ s.Corr)
    (hleftValue : leftValue ≠ -1) (hrightValue : rightValue ≠ -1)
    (hCorr : s'.Corr = s.Corr)
    (hleft : left s' = Finmap.insert p leftValue (left s))
    (hright : right s' = Finmap.insert p rightValue (right s)) :
    ∀ q ∈ s'.Corr,
      (Finmap.lookupD q (left s') = -1) =
        (Finmap.lookupD q (right s') = -1) := by
  intro q hq
  rw [hCorr] at hq
  rw [hleft, hright]
  by_cases hqp : q = p
  · subst q
    simp [hleftValue, hrightValue]
  · simp only [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma next_preserves_locked_round_iff_locked_value {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hinv : all_locked_round_iff_locked_value s)
    (hnext : Next s s') :
    all_locked_round_iff_locked_value s' := by
  unfold all_locked_round_iff_locked_value at hinv ⊢
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, hCorr, _, _, _, _, _, _, _, _, _, _, hlockedValue,
        hlockedRound, _⟩
    exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hproposals, hprevotes⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, hvalidValue,
          hvalidRound, haction⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with ⟨_, hleft, hright, _, _⟩
        apply nil_iff_maps_insert
          (left := fun x => x.locked_round)
          (right := fun x => x.locked_value)
          (leftValue := Finmap.lookupD p s.round)
          (rightValue := v) hinv hp
        · have hrange :=
            ((ind_type_ok_iff_components s).mp htype).round_values p hp
          simp only [Finset.mem_Icc] at hrange
          omega
        · exact fun heq =>
            hmodel.2.2.2.2.2.2.2.2.1 (heq ▸ hv)
        · exact hCorr
        · exact hright
        · exact hleft
      · rcases hstay with ⟨_, hleft, hright, _, _⟩
        apply nil_iff_maps_frame hinv hCorr hright hleft
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, _, hCorr, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold on_timeout_propose at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, _, hCorr, _, _, _, _, _, _, _, _, hlockedValue,
          hlockedRound, _⟩
      exact nil_iff_maps_frame hinv hCorr hlockedRound hlockedValue

lemma next_preserves_valid_round_iff_valid_value {s s' : State}
    (hmodel : model_assumptions s) (htype : ind_type_ok s)
    (hinv : all_valid_round_iff_valid_value s)
    (hnext : Next s s') :
    all_valid_round_iff_valid_value s' := by
  unfold all_valid_round_iff_valid_value at hinv ⊢
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, hCorr, _, _, _, _, _, _, _, _, _, _, _, _,
        hvalidValue, hvalidRound, _⟩
    exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hstep, hdecision, hlockedValue,
          hlockedRound, hvalidValue, hvalidRound, hprevote, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprevotes⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hproposals, hprevotes⟩
      rcases hact with
        ⟨_, _, v, hv, _, vr, hvr, _, _, hbranch, hvalidValue,
          hvalidRound, haction⟩
      apply nil_iff_maps_insert
        (left := fun x => x.valid_round)
        (right := fun x => x.valid_value)
        (leftValue := Finmap.lookupD p s.round)
        (rightValue := v) hinv hp
      · have hrange :=
          ((ind_type_ok_iff_components s).mp htype).round_values p hp
        simp only [Finset.mem_Icc] at hrange
        omega
      · exact fun heq =>
          hmodel.2.2.2.2.2.2.2.2.1 (heq ▸ hv)
      · exact hCorr
      · exact hvalidRound
      · exact hvalidValue
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hdecision, hlockedValue, hlockedRound, hvalidValue,
          hvalidRound, hproposals, hprevotes, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, _, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hlockedValue, hlockedRound, hvalidValue,
          hvalidRound, hproposals, hprevotes, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold on_timeout_propose at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprevotes⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, _, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hdecision, hlockedValue, hlockedRound, hvalidValue,
          hvalidRound, hproposals, hprevotes, hprecommit⟩
      exact nil_iff_maps_frame hinv hCorr hvalidRound hvalidValue

lemma bounded_rounds_frame {s s' : State}
    (hinv : all_valid_and_locked_round_bounded s)
    (hCorr : s'.Corr = s.Corr) (hround : s'.round = s.round)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hlockedRound : s'.locked_round = s.locked_round) :
    all_valid_and_locked_round_bounded s' := by
  unfold all_valid_and_locked_round_bounded at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  simpa [hround, hvalidRound, hlockedRound] using hinv q hq

lemma bounded_rounds_advance {s s' : State} {p newRound : Int}
    (hinv : all_valid_and_locked_round_bounded s) (hp : p ∈ s.Corr)
    (hadvance : Finmap.lookupD p s.round ≤ newRound)
    (hCorr : s'.Corr = s.Corr)
    (hround : s'.round = Finmap.insert p newRound s.round)
    (hvalidRound : s'.valid_round = s.valid_round)
    (hlockedRound : s'.locked_round = s.locked_round) :
    all_valid_and_locked_round_bounded s' := by
  unfold all_valid_and_locked_round_bounded at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  rw [hround, hvalidRound, hlockedRound]
  by_cases hqp : q = p
  · subst q
    simp only [lookupD_insert_self]
    have hold := hinv p hp
    omega
  · rw [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma bounded_rounds_set_valid {s s' : State} {p : Int}
    (hinv : all_valid_and_locked_round_bounded s) (hp : p ∈ s.Corr)
    (hCorr : s'.Corr = s.Corr) (hround : s'.round = s.round)
    (hvalidRound :
      s'.valid_round =
        Finmap.insert p (Finmap.lookupD p s.round) s.valid_round)
    (hlockedRound : s'.locked_round = s.locked_round) :
    all_valid_and_locked_round_bounded s' := by
  unfold all_valid_and_locked_round_bounded at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  rw [hround, hvalidRound, hlockedRound]
  by_cases hqp : q = p
  · subst q
    simp only [lookupD_insert_self]
    exact ⟨le_rfl, (hinv p hp).2⟩
  · rw [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma bounded_rounds_set_valid_and_locked {s s' : State} {p : Int}
    (hinv : all_valid_and_locked_round_bounded s) (hp : p ∈ s.Corr)
    (hCorr : s'.Corr = s.Corr) (hround : s'.round = s.round)
    (hvalidRound :
      s'.valid_round =
        Finmap.insert p (Finmap.lookupD p s.round) s.valid_round)
    (hlockedRound :
      s'.locked_round =
        Finmap.insert p (Finmap.lookupD p s.round) s.locked_round) :
    all_valid_and_locked_round_bounded s' := by
  unfold all_valid_and_locked_round_bounded at hinv ⊢
  intro q hq
  rw [hCorr] at hq
  rw [hround, hvalidRound, hlockedRound]
  by_cases hqp : q = p
  · subst q
    simp
  · simp only [lookupD_insert_of_ne hqp]
    exact hinv q hq

lemma next_preserves_valid_and_locked_round_bounded {s s' : State}
    (hinv : all_valid_and_locked_round_bounded s)
    (hnext : Next s s') :
    all_valid_and_locked_round_bounded s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, _, hCorr, _, _, _, _, _, _, _, hround, _, _, _, hlockedRound,
        _, hvalidRound, _⟩
    exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hstep, hdecision, hlockedValue,
          hlockedRound, hvalidValue, hvalidRound, hprevote, hprecommit⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, hround, _, _, hlockedRound,
          _, hvalidRound, _⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, hround, _, _, hlockedRound,
          _, hvalidRound, _⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, hround, _, _, hlockedRound,
          _, hvalidRound, _⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, hCorr, _, _, _, _, _, _, _, hround, _, _, _⟩
      rcases hact with
        ⟨_, _, _, _, _, _, _, _, _, hbranch, _, hvalidRound, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with ⟨_, _, hlockedRound, _, _⟩
        exact bounded_rounds_set_valid_and_locked
          hinv hp hCorr hround hvalidRound hlockedRound
      · rcases hstay with ⟨_, _, hlockedRound, _, _⟩
        exact bounded_rounds_set_valid
          hinv hp hCorr hround hvalidRound hlockedRound
    · unfold upon_quorum_of_precommits_any at h
      rcases h with
        ⟨hact, hCorr, _, _, _, _, _, _, _, _, _, hlockedRound, _,
          hvalidRound, _⟩
      rcases hact with
        ⟨_, _, _, _, _, _, hround, _, _⟩
      apply bounded_rounds_advance hinv hp (newRound :=
        Finmap.lookupD p s.round + 1) (by omega)
        hCorr hround hvalidRound hlockedRound
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with
        ⟨_, _, _, hCorr, _, _, _, _, _, _, _, hround, _, hlockedRound,
          _, hvalidRound, _⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold on_timeout_propose at h
      rcases h with
        ⟨_, hCorr, _, _, _, _, _, _, _, hround, _, _, hlockedRound,
          _, hvalidRound, _⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨_, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hround, hdecision, hlockedValue, hlockedRound,
          hvalidValue, hvalidRound, hproposals, hprevotes⟩
      exact bounded_rounds_frame hinv hCorr hround hvalidRound hlockedRound
    · unfold on_round_catchup at h
      rcases h with
        ⟨_, hact, hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax,
          hProposer, hdecision, hlockedValue, hlockedRound, hvalidValue,
          hvalidRound, hproposals, hprevotes, hprecommit⟩
      rcases hact with
        ⟨rnd, _, _, _, _, _, _, _, _, _, _, hgreater, _, _, hround, _, _⟩
      exact bounded_rounds_advance hinv hp (by omega)
        hCorr hround hvalidRound hlockedRound

lemma decided_proposal_transfer_at {s s' : State}
    (hold : all_if_in_decided_then_received_proposal s)
    (hdecOld : all_if_in_decided_then_valid_decision s)
    (hdecNew : all_if_in_decided_then_valid_decision s')
    (hmono : MessagesMonotone s s')
    (hCorr : s'.Corr = s.Corr) (hValid : s'.ValidValues = s.ValidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hProposer : s'.Proposer = s.Proposer)
    {q : Int} (hq : q ∈ s'.Corr)
    (hstep : Finmap.lookupD q s'.step = Step.DECIDED)
    (hdecision :
      Finmap.lookupD q s'.decision = Finmap.lookupD q s.decision) :
    ∃ r ∈ Finset.Icc 0 s'.MaxRound,
      ∃ m ∈ Finmap.lookupD r s'.msgs_propose,
        m.src = Finmap.lookupD r s'.Proposer ∧
          m.proposal = Finmap.lookupD q s'.decision := by
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  have hvalidNew : Finmap.lookupD q s'.decision ∈ s'.ValidValues :=
    Eq.mp (hdecNew q hq) hstep
  have hvalidOld : Finmap.lookupD q s.decision ∈ s.ValidValues := by
    simpa [hValid, hdecision] using hvalidNew
  have hstepOld : Finmap.lookupD q s.step = Step.DECIDED :=
    Eq.mpr (hdecOld q hqOld) hvalidOld
  obtain ⟨r, hr, m, hm, hsrc, hproposal⟩ :=
    hold q hqOld hstepOld
  exact ⟨r, by simpa [hMax] using hr, m, hmono.proposals r hm,
    by simpa [hProposer] using hsrc, by simpa [hdecision] using hproposal⟩

lemma next_preserves_decided_received_proposal {s s' : State}
    (hold : all_if_in_decided_then_received_proposal s)
    (hdecOld : all_if_in_decided_then_valid_decision s)
    (hnext : Next s s') :
    all_if_in_decided_then_received_proposal s' := by
  have hdecNew := next_preserves_decided_valid hdecOld hnext
  have hmono := next_messages_monotone hnext
  have hparams := next_same_parameters hnext
  rcases hparams with
    ⟨hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax, hProposer⟩
  unfold all_if_in_decided_then_received_proposal
  intro q hq hstep
  rcases next_decision_evolution hnext with hframe |
    ⟨p, value, round, validRound, hp, hvalue, hround, hvalidRound,
      hproposal, hquorum, hdecision, hstepUpdate⟩
  · exact decided_proposal_transfer_at hold hdecOld hdecNew hmono
      hCorr hValid hMax hProposer hq hstep
      (by simp [hframe])
  · by_cases hqp : q = p
    · subst q
      refine ⟨round, by simpa [hMax] using hround,
        ProposalMsg.mk value round
          (Finmap.lookupD round s.Proposer) validRound,
        hmono.proposals round hproposal, ?_, ?_⟩
      · simp [hProposer]
      · simp [hdecision]
    · apply decided_proposal_transfer_at hold hdecOld hdecNew hmono
        hCorr hValid hMax hProposer hq hstep
      rw [hdecision, lookupD_insert_of_ne hqp]

lemma decided_quorum_transfer_at {s s' : State}
    (hold : all_if_in_decided_then_received_two_thirds s)
    (hdecOld : all_if_in_decided_then_valid_decision s)
    (hdecNew : all_if_in_decided_then_valid_decision s')
    (hmono : MessagesMonotone s s')
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hMax : s'.MaxRound = s.MaxRound) (hT : s'.T = s.T)
    {q : Int} (hq : q ∈ s'.Corr)
    (hstep : Finmap.lookupD q s'.step = Step.DECIDED)
    (hdecision :
      Finmap.lookupD q s'.decision = Finmap.lookupD q s.decision) :
    ∃ r ∈ Finset.Icc 0 s'.MaxRound,
      (pc_set s' r (Finmap.lookupD q s'.decision)).card ≥
        2 * s'.T + 1 := by
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  have hvalidNew : Finmap.lookupD q s'.decision ∈ s'.ValidValues :=
    Eq.mp (hdecNew q hq) hstep
  have hvalidOld : Finmap.lookupD q s.decision ∈ s.ValidValues := by
    simpa [hValid, hdecision] using hvalidNew
  have hstepOld : Finmap.lookupD q s.step = Step.DECIDED :=
    Eq.mpr (hdecOld q hqOld) hvalidOld
  obtain ⟨r, hr, hcardRaw⟩ := hold q hqOld hstepOld
  have hcardOld :
      (pc_set s r (Finmap.lookupD q s.decision)).card ≥
        2 * s.T + 1 := by
    simpa [pc_set, vote_senders, votes_for, all_replicas, eq_comm]
      using hcardRaw
  have hsub :
      pc_set s r (Finmap.lookupD q s.decision) ⊆
        pc_set s' r (Finmap.lookupD q s.decision) :=
    pc_set_mono_frame hCorr hFaulty (hmono.precommits r)
  have hcardLe := Finset.card_le_card hsub
  refine ⟨r, by simpa [hMax] using hr, ?_⟩
  rw [hdecision]
  omega

lemma next_preserves_decided_received_two_thirds {s s' : State}
    (htype : ind_type_ok s)
    (hold : all_if_in_decided_then_received_two_thirds s)
    (hdecOld : all_if_in_decided_then_valid_decision s)
    (hnext : Next s s') :
    all_if_in_decided_then_received_two_thirds s' := by
  have hdecNew := next_preserves_decided_valid hdecOld hnext
  have hmono := next_messages_monotone hnext
  have hparams := next_same_parameters hnext
  rcases hparams with
    ⟨hCorr, hFaulty, hN, hT, hValid, hInvalid, hMax, hProposer⟩
  unfold all_if_in_decided_then_received_two_thirds
  intro q hq hstep
  rcases next_decision_evolution hnext with hframe |
    ⟨p, value, round, validRound, hp, hvalue, hround, hvalidRound,
      hproposal, hquorum, hdecision, hstepUpdate⟩
  · obtain ⟨r, hr, hcard⟩ :=
      decided_quorum_transfer_at hold hdecOld hdecNew hmono hCorr
        hFaulty hValid hMax hT hq hstep (by simp [hframe])
    refine ⟨r, hr, ?_⟩
    simpa [pc_set, vote_senders, votes_for, all_replicas, eq_comm]
      using hcard
  · by_cases hqp : q = p
    · subst q
      have hcardOld :
          (pc_set s round value).card ≥
            2 * s.T + 1 := by
        rw [← precommit_value_messages_card_eq_pc_set
          htype hround]
        exact hquorum
      have hsub :=
        pc_set_mono_frame hCorr hFaulty
          (hmono.precommits round)
          (v := value)
      have hcardLe := Finset.card_le_card hsub
      refine ⟨round, by simpa [hMax] using hround, ?_⟩
      have hcardNew :
          (pc_set s' round value).card ≥
            2 * s'.T + 1 := by
        omega
      simpa [pc_set, vote_senders, votes_for, all_replicas,
        hdecision, eq_comm] using hcardNew
    · obtain ⟨r, hr, hcard⟩ :=
        decided_quorum_transfer_at hold hdecOld hdecNew hmono hCorr
          hFaulty hValid hMax hT hq hstep
          (by rw [hdecision, lookupD_insert_of_ne hqp])
      refine ⟨r, hr, ?_⟩
      simpa [pc_set, vote_senders, votes_for, all_replicas, eq_comm]
        using hcard

lemma next_preserves_no_future_messages {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hold : all_no_future_messages_sent s)
    (hnext : Next s s') :
    all_no_future_messages_sent s' := by
  have htNew := (ind_type_ok_iff_components s').mp
    (next_preserves_ind_type_ok htype hnext)
  have hev := next_source_evolution hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, _, _, _, hMax, hProposer⟩
  have hdisj : s.Corr ∩ s.Faulty = ∅ := by
    unfold model_assumptions at hmodel
    exact hmodel.2.2.2.1
  unfold all_no_future_messages_sent at hold ⊢
  intro q hq
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  have hqNotFaulty : q ∉ s.Faulty := by
    intro hqf
    have : q ∈ s.Corr ∩ s.Faulty := by simp [hqOld, hqf]
    simpa [hdisj] using this
  have hrangeNew :
      Finmap.lookupD q s'.round ∈ Finset.Icc 0 s'.MaxRound :=
    htNew.round_values q hq
  have hroundMono := hev.round_mono q hqOld
  obtain ⟨⟨hpropOld, hpvOld, hpcOld⟩, hfutureOld⟩ :=
    hold q hqOld
  have oldFuture (r : Int)
      (hrange : r ∈ Finset.Icc 0 s.MaxRound)
      (hgt : r > Finmap.lookupD q s.round) :=
      hfutureOld r (by simp [hrange, hgt])
  constructor
  · constructor
    · by_cases hpropNew :
          q = Finmap.lookupD (Finmap.lookupD q s'.round) s'.Proposer
      · exact Or.inl hpropNew
      · right
        intro m hm hsrc
        rcases hev.proposals _ m hm with hmOld | hmFaulty | hmNew
        · by_cases hre :
              Finmap.lookupD q s'.round = Finmap.lookupD q s.round
          · rcases hpropOld with hpropOld | hnone
            · apply hpropNew
              simpa [hre, hProposer] using hpropOld
            · exact hnone m (by simpa [hre] using hmOld) hsrc
          · have hgt :
                Finmap.lookupD q s'.round >
                  Finmap.lookupD q s.round := by omega
            have hf := oldFuture (Finmap.lookupD q s'.round)
              (by simpa [hMax] using hrangeNew) hgt
            exact hf.1 m hmOld hsrc
        · apply hqNotFaulty
          simpa [hsrc] using hmFaulty
        · rcases hmNew with ⟨_, hr, hproposer⟩
          apply hpropNew
          simpa [hsrc, hProposer] using hproposer
    · constructor
      · by_cases hpv :
          Finmap.lookupD q s'.step = Step.PREVOTE
        · exact Or.inl hpv
        · by_cases hpc :
            Finmap.lookupD q s'.step = Step.PRECOMMIT
          · exact Or.inr (Or.inl hpc)
          · by_cases hdec :
              Finmap.lookupD q s'.step = Step.DECIDED
            · exact Or.inr (Or.inr (Or.inl hdec))
            · right; right; right
              intro m hm hsrc
              rcases hev.prevotes _ m hm with hmOld | hmFaulty | hmNew
              · by_cases hre :
                    Finmap.lookupD q s'.round =
                      Finmap.lookupD q s.round
                · rcases hpvOld with hs | hs | hs | hnone
                  · have hn :=
                      (next_step_progress_same_round hnext hre).1
                        (Or.inl hs)
                    rcases hn with hn | hn | hn <;> contradiction
                  · have hn :=
                      (next_step_progress_same_round hnext hre).1
                        (Or.inr (Or.inl hs))
                    rcases hn with hn | hn | hn <;> contradiction
                  · have hn :=
                      (next_step_progress_same_round hnext hre).1
                        (Or.inr (Or.inr hs))
                    rcases hn with hn | hn | hn <;> contradiction
                  · exact hnone m (by simpa [hre] using hmOld) hsrc
                · have hgt :
                      Finmap.lookupD q s'.round >
                        Finmap.lookupD q s.round := by omega
                  exact (oldFuture (Finmap.lookupD q s'.round)
                    (by simpa [hMax] using hrangeNew) hgt).2.1
                      m hmOld hsrc
              · apply hqNotFaulty
                simpa [hsrc] using hmFaulty
              · exact hpv (by simpa [hsrc] using hmNew.2.2)
      · by_cases hpc :
          Finmap.lookupD q s'.step = Step.PRECOMMIT
        · exact Or.inl hpc
        · by_cases hdec :
            Finmap.lookupD q s'.step = Step.DECIDED
          · exact Or.inr (Or.inl hdec)
          · right; right
            intro m hm hsrc
            rcases hev.precommits _ m hm with hmOld | hmFaulty | hmNew
            · by_cases hre :
                  Finmap.lookupD q s'.round =
                    Finmap.lookupD q s.round
              · rcases hpcOld with hs | hs | hnone
                · have hn :=
                    (next_step_progress_same_round hnext hre).2
                      (Or.inl hs)
                  rcases hn with hn | hn <;> contradiction
                · have hn :=
                    (next_step_progress_same_round hnext hre).2
                      (Or.inr hs)
                  rcases hn with hn | hn <;> contradiction
                · exact hnone m (by simpa [hre] using hmOld) hsrc
              · have hgt :
                    Finmap.lookupD q s'.round >
                      Finmap.lookupD q s.round := by omega
                exact (oldFuture (Finmap.lookupD q s'.round)
                  (by simpa [hMax] using hrangeNew) hgt).2.2
                    m hmOld hsrc
            · apply hqNotFaulty
              simpa [hsrc] using hmFaulty
            · exact hpc (by simpa [hsrc] using hmNew.2.2)
  · intro r hr
    have hrange : r ∈ Finset.Icc 0 s.MaxRound := by
      simpa [hMax] using (Finset.mem_filter.mp hr).1
    have hgtNew : r > Finmap.lookupD q s'.round :=
      (Finset.mem_filter.mp hr).2
    have hgtOld : r > Finmap.lookupD q s.round := by omega
    have hf := oldFuture r hrange hgtOld
    constructor
    · intro m hm hsrc
      rcases hev.proposals r m hm with hmOld | hmFaulty | hmNew
      · exact hf.1 m hmOld hsrc
      · apply hqNotFaulty
        simpa [hsrc] using hmFaulty
      · have hrOld := hmNew.2.1
        rw [← hsrc] at hrOld
        omega
    · constructor
      · intro m hm hsrc
        rcases hev.prevotes r m hm with hmOld | hmFaulty | hmNew
        · exact hf.2.1 m hmOld hsrc
        · apply hqNotFaulty
          simpa [hsrc] using hmFaulty
        · have hrOld := hmNew.2.1
          rw [← hsrc] at hrOld
          omega
      · intro m hm hsrc
        rcases hev.precommits r m hm with hmOld | hmFaulty | hmNew
        · exact hf.2.2 m hmOld hsrc
        · apply hqNotFaulty
          simpa [hsrc] using hmFaulty
        · have hrOld := hmNew.2.1
          rw [← hsrc] at hrOld
          omega

lemma next_preserves_valid_round_quorum {s s' : State}
    (htype : ind_type_ok s)
    (hold : all_if_valid_round_then_two_thirds_prevotes s)
    (hnext : Next s s') :
    all_if_valid_round_then_two_thirds_prevotes s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, hValid, _, _, _⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  unfold all_if_valid_round_then_two_thirds_prevotes at hold ⊢
  intro q hq hnonNil
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_valid_evolution hnext with
    ⟨hvalidValue, hvalidRound⟩ |
    ⟨p, value, hp, hvalue, hvalidValue, hvalidRound,
      hquorum, hstep, hsent⟩
  · have hcardOld := hold q hqOld (by simpa [hvalidRound] using hnonNil)
    have hsub := pv_set_mono_frame hCorr hFaulty
      (hmono.prevotes (Finmap.lookupD q s.valid_round))
      (v := Finmap.lookupD q s.valid_value)
    have hcardLe := Finset.card_le_card hsub
    simpa [pv_set, vote_senders, votes_for, all_replicas,
      hvalidRound, hvalidValue, hT, eq_comm] using
      (show (pv_set s' (Finmap.lookupD q s.valid_round)
        (Finmap.lookupD q s.valid_value)).card ≥ 2 * s'.T + 1 by
          have hraw :
              (pv_set s (Finmap.lookupD q s.valid_round)
                (Finmap.lookupD q s.valid_value)).card ≥
                2 * s.T + 1 := by
            simpa [pv_set, vote_senders, votes_for, all_replicas,
              eq_comm] using hcardOld
          omega)
  · by_cases hqp : q = p
    · subst q
      have hrange := ht.round_values p hp
      have hcardOld : (pv_set s (Finmap.lookupD p s.round) value).card ≥
          2 * s.T + 1 := by
        rw [← prevote_value_messages_card_eq_pv_set htype hrange]
        exact hquorum
      have hsub := pv_set_mono_frame hCorr hFaulty
        (hmono.prevotes (Finmap.lookupD p s.round)) (v := value)
      have hcardLe := Finset.card_le_card hsub
      have hcardNew :
          (pv_set s' (Finmap.lookupD p s.round) value).card ≥
            2 * s'.T + 1 := by omega
      simpa [pv_set, vote_senders, votes_for, all_replicas,
        hvalidRound, hvalidValue, eq_comm] using hcardNew
    · have hcardOld := hold q hqOld (by
        simpa [hvalidRound, lookupD_insert_of_ne hqp] using hnonNil)
      have hsub := pv_set_mono_frame hCorr hFaulty
        (hmono.prevotes (Finmap.lookupD q s.valid_round))
        (v := Finmap.lookupD q s.valid_value)
      have hcardLe := Finset.card_le_card hsub
      have hraw :
          (pv_set s (Finmap.lookupD q s.valid_round)
            (Finmap.lookupD q s.valid_value)).card ≥ 2 * s.T + 1 := by
        simpa [pv_set, vote_senders, votes_for, all_replicas,
          eq_comm] using hcardOld
      have hnew :
          (pv_set s' (Finmap.lookupD q s.valid_round)
            (Finmap.lookupD q s.valid_value)).card ≥ 2 * s'.T + 1 := by
        omega
      simpa [pv_set, vote_senders, votes_for, all_replicas,
        hvalidRound, hvalidValue, lookupD_insert_of_ne hqp,
        eq_comm] using hnew

lemma next_preserves_locked_sent_commit {s s' : State}
    (htype : ind_type_ok s)
    (hold : all_if_locked_round_then_sent_commit s)
    (hnext : Next s s') :
    all_if_locked_round_then_sent_commit s' := by
  have hmono := next_messages_monotone hnext
  have hsource := next_source_evolution hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, _, _, hMax, _⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  unfold all_if_locked_round_then_sent_commit at hold ⊢
  intro q hq hnonNil
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_locked_evolution hnext with
    ⟨hlockedValue, hlockedRound⟩ |
    ⟨p, value, hp, hvalue, hlockedValue, hlockedRound,
      hvalidRound, hsent⟩
  · obtain ⟨r, hr, hrle, m, hm, hsrc, hid⟩ :=
      hold q hqOld (by simpa [hlockedRound] using hnonNil)
    refine ⟨r, by simpa [hMax] using hr, ?_, m,
      hmono.precommits r hm, hsrc, ?_⟩
    · have := hsource.round_mono q hqOld
      omega
    · simpa [hlockedValue] using hid
  · by_cases hqp : q = p
    · subst q
      have hrange := ht.round_values p hp
      refine ⟨Finmap.lookupD p s.round, by simpa [hMax] using hrange,
        hsource.round_mono p hp,
        VoteMsg.mk value VoteKind.PRECOMMIT
          (Finmap.lookupD p s.round) p, hsent, rfl, ?_⟩
      simp [hlockedValue]
    · obtain ⟨r, hr, hrle, m, hm, hsrc, hid⟩ :=
        hold q hqOld (by
          simpa [hlockedRound, lookupD_insert_of_ne hqp] using hnonNil)
      refine ⟨r, by simpa [hMax] using hr, ?_, m,
        hmono.precommits r hm, hsrc, ?_⟩
      · have := hsource.round_mono q hqOld
        omega
      · simpa [hlockedValue, lookupD_insert_of_ne hqp] using hid

lemma next_preserves_locked_below_valid {s s' : State}
    (hold : all_locked_round_below_valid_round s)
    (hbound : all_valid_and_locked_round_bounded s)
    (hnext : Next s s') :
    all_locked_round_below_valid_round s' := by
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, _, _, _, _⟩
  unfold all_locked_round_below_valid_round at hold ⊢
  intro q hq
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_locked_evolution hnext with
    ⟨hlockedValue, hlockedRound⟩ |
    ⟨p, value, hp, hvalue, hlockedValue, hlockedRound,
      hvalidRound, hsent⟩
  · rcases next_valid_evolution hnext with
      ⟨hvalidValue, hvalidRound⟩ |
      ⟨p, value, hp, hvalue, hvalidValue, hvalidRound,
        hquorum, hstep, hsent⟩
    · simpa [hlockedRound, hvalidRound] using hold q hqOld
    · by_cases hqp : q = p
      · subst q
        have hlockedValid := hold p hp
        have hvalidRoundBound := (hbound p hp).1
        simp [hvalidRound, hlockedRound]
        omega
      · simpa [hvalidRound, hlockedRound,
          lookupD_insert_of_ne hqp] using hold q hqOld
  · by_cases hqp : q = p
    · subst q
      simp [hlockedRound, hvalidRound]
    · simpa [hlockedRound, hvalidRound,
        lookupD_insert_of_ne hqp] using hold q hqOld

lemma next_preserves_valid_precommitted {s s' : State}
    (hold : all_if_valid_round_then_precommitted s)
    (hprecommitStep : all_if_in_precommit_then_sent_precommit s)
    (hnext : Next s s') :
    all_if_valid_round_then_precommitted s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, _, _, _, _⟩
  unfold all_if_valid_round_then_precommitted at hold ⊢
  intro q hq hnonNil
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_valid_evolution hnext with
    ⟨hvalidValue, hvalidRound⟩ |
    ⟨p, value, hp, hvalue, hvalidValue, hvalidRound,
      hquorum, hstep, hsent⟩
  · obtain ⟨m, hm, hsrc⟩ :=
      hold q hqOld (by simpa [hvalidRound] using hnonNil)
    exact ⟨m, by simpa [hvalidRound] using hmono.precommits _ hm,
      hsrc⟩
  · by_cases hqp : q = p
    · subst q
      rcases hsent with hsent | ⟨hstepOld, hprecommits⟩
      · rcases hsent with ⟨m, hm, hsrc, hid⟩
        exact ⟨m, by simpa [hvalidRound] using hm, hsrc⟩
      · rcases hprecommitStep p hp hstepOld with ⟨m, hm, hid, hsrc⟩
        exact ⟨m, by simpa [hvalidRound, hprecommits] using hm, hsrc⟩
    · obtain ⟨m, hm, hsrc⟩ :=
        hold q hqOld (by
          simpa [hvalidRound, lookupD_insert_of_ne hqp] using hnonNil)
      exact ⟨m, by
        simpa [hvalidRound, lookupD_insert_of_ne hqp] using
          hmono.precommits _ hm, hsrc⟩

lemma next_preserves_valid_current_precommitted {s s' : State}
    (hold : all_valid_in_current_round_precommitted s)
    (hbound : all_valid_and_locked_round_bounded s)
    (hnext : Next s s') :
    all_valid_in_current_round_precommitted s' := by
  rcases next_same_parameters hnext with
    ⟨hCorr, _, _, _, _, _, _, _⟩
  have hevSource := next_source_evolution hnext
  unfold all_valid_in_current_round_precommitted at hold ⊢
  intro q hq heq
  have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
  rcases next_valid_evolution hnext with
    ⟨hvalidValue, hvalidRound⟩ |
    ⟨p, value, hp, hvalue, hvalidValue, hvalidRound,
      hquorum, hstep, hsent⟩
  · have hle := (hbound q hqOld).1
    have hmono := hevSource.round_mono q hqOld
    have hre :
        Finmap.lookupD q s'.round = Finmap.lookupD q s.round := by
      rw [hvalidRound] at heq
      omega
    exact (next_step_progress_same_round hnext hre).2
      (hold q hqOld (by simpa [hvalidRound, hre] using heq))
  · by_cases hqp : q = p
    · subst q
      exact Or.inl hstep
    · have hle := (hbound q hqOld).1
      have hmono := hevSource.round_mono q hqOld
      have hre :
          Finmap.lookupD q s'.round = Finmap.lookupD q s.round := by
        rw [hvalidRound, lookupD_insert_of_ne hqp] at heq
        omega
      exact (next_step_progress_same_round hnext hre).2
        (hold q hqOld (by
          simpa [hvalidRound, lookupD_insert_of_ne hqp, hre] using heq))

lemma next_preserves_correct_proposal_round {s s' : State}
    (htype : ind_type_ok s)
    (hbound : all_valid_and_locked_round_bounded s)
    (hvalidCurrent : all_valid_in_current_round_precommitted s)
    (hold : all_correct_proposal_valid_round_below_round s)
    (hmodel : model_assumptions s)
    (hnext : Next s s') :
    all_correct_proposal_valid_round_below_round s' := by
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, _, hValid, _, hMax, _⟩
  have hdisj : s.Corr ∩ s.Faulty = ∅ := hmodel.2.2.2.1
  have transfer (hproposals : s'.msgs_propose = s.msgs_propose) :
      all_correct_proposal_valid_round_below_round s' := by
    unfold all_correct_proposal_valid_round_below_round at hold ⊢
    intro r hr m hm hsrc
    exact hold r (by simpa [hMax] using hr) m
      (by simpa [hproposals] using hm) (by simpa [hCorr] using hsrc)
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with
      ⟨_, ⟨r₀, hr₀, _, ⟨fps, hfps, _, value, hvalue, _, vr, hvr,
        hproposals⟩, _⟩, _, hFaultyEq, _, _, _, _, hMaxEq, _⟩
    unfold all_correct_proposal_valid_round_below_round at hold ⊢
    intro r hr m hm hsrc
    rw [hproposals, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact hold r (by simpa [hMaxEq] using hr) m hm
        (by simpa [hCorr] using hsrc)
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hsrcFaulty : src ∈ s.Faulty :=
        Finset.mem_powerset.mp hfps hsrcFps
      have hsrcCorr : src ∈ s.Corr := by simpa [hCorr] using hsrc
      have : src ∈ s.Corr ∩ s.Faulty := by simp [hsrcCorr, hsrcFaulty]
      simpa [hdisj] using this
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _⟩
      rcases hact with
        ⟨_, hstepOld, _, _, value, hvalue, hproposals, _⟩
      unfold all_correct_proposal_valid_round_below_round at hold ⊢
      intro r hr m hm hsrc
      rw [hproposals, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hroundEq, hm⟩
      · exact hold r (by simpa [hMax] using hr) m hm
          (by simpa [hCorr] using hsrc)
      · simp at hm
        subst m
        have hle :=
          (hbound p hp).1
        have hne :
            Finmap.lookupD p s.valid_round ≠ Finmap.lookupD p s.round := by
          intro heq
          rcases hvalidCurrent p hp heq with hs | hs
          · rw [hstepOld] at hs
            contradiction
          · rw [hstepOld] at hs
            contradiction
        change r > Finmap.lookupD p s.valid_round
        omega
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hproposals, _⟩
      exact transfer hproposals
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact transfer hproposals

lemma next_preserves_precommit_has_prevote {s s' : State}
    (hmodel : model_assumptions s)
    (hold : if_sent_precommit_then_sent_prevote s)
    (hprevoteStep : all_if_in_prevote_then_sent_prevote s)
    (hnext : Next s s') :
    if_sent_precommit_then_sent_prevote s' := by
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, _, _, _, hMax, _⟩
  have hmono := next_messages_monotone hnext
  have transfer (hprecommits : s'.msgs_precommit = s.msgs_precommit) :
      if_sent_precommit_then_sent_prevote s' := by
    unfold if_sent_precommit_then_sent_prevote at hold ⊢
    intro r hr m hm hsrc
    obtain ⟨pv, hpv, hsrcPv⟩ :=
      hold r (by simpa [hMax] using hr) m
        (by simpa [hprecommits] using hm)
        (by simpa [hCorr] using hsrc)
    exact ⟨pv, hmono.prevotes r hpv, hsrcPv⟩
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, ⟨r₀, hr₀, hrest⟩, hCorrEq, hFaultyEq, _, _, _, _,
      hMaxEq, _⟩ := hfaulty
    obtain ⟨_, _, _, _, _, hblock⟩ := hrest
    obtain ⟨fps, hfps, _, value, hvalue, hprecommits⟩ := hblock
    unfold if_sent_precommit_then_sent_prevote at hold ⊢
    intro r hr m hm hsrc
    rw [hprecommits, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · obtain ⟨pv, hpv, hsrcPv⟩ :=
        hold r (by simpa [hMaxEq] using hr) m hm
          (by simpa [hCorrEq] using hsrc)
      exact ⟨pv, hmono.prevotes r hpv, hsrcPv⟩
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hsrcFaulty : src ∈ s.Faulty :=
        Finset.mem_powerset.mp hfps hsrcFps
      have hsrcCorr : src ∈ s.Corr := by simpa [hCorrEq] using hsrc
      have hboth : src ∈ s.Corr ∩ s.Faulty := by
        simp [hsrcCorr, hsrcFaulty]
      simpa [hmodel.2.2.2.1] using hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact transfer hprecommits
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact transfer hprecommits
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact transfer hprecommits
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes⟩
      rcases hact with
        ⟨hstepOld, _, evidence, _, _, hprecommits, _, _⟩
      unfold if_sent_precommit_then_sent_prevote at hold ⊢
      intro r hr m hm hsrc
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · obtain ⟨pv, hpv, hsrcPv⟩ :=
          hold r (by simpa [hMax] using hr) m hm
            (by simpa [hCorr] using hsrc)
        exact ⟨pv, by simpa [hprevotes] using hpv, hsrcPv⟩
      · simp at hm
        subst m
        rcases hprevoteStep p hp hstepOld with ⟨pv, hpv, _, hsrcPv⟩
        exact ⟨pv, by rw [hrEq]; simpa [hprevotes] using hpv,
          hsrcPv.symm⟩
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, hprevotes⟩
      rcases hact with
        ⟨hstepOld, _, value, hvalue, _, _, _, _, _, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with
          ⟨hstepPrevote, _, _, hprecommits, _⟩
        unfold if_sent_precommit_then_sent_prevote at hold ⊢
        intro r hr m hm hsrc
        rw [hprecommits, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hrEq, hm⟩
        · obtain ⟨pv, hpv, hsrcPv⟩ :=
            hold r (by simpa [hMax] using hr) m hm
              (by simpa [hCorr] using hsrc)
          exact ⟨pv, by simpa [hprevotes] using hpv, hsrcPv⟩
        · simp at hm
          subst m
          rcases hprevoteStep p hp hstepPrevote with
            ⟨pv, hpv, _, hsrcPv⟩
          exact ⟨pv, by rw [hrEq]; simpa [hprevotes] using hpv,
            hsrcPv.symm⟩
      · rcases hstay with ⟨_, _, _, hprecommits, _⟩
        exact transfer hprecommits
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact transfer hprecommits
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hprecommits⟩
      exact transfer hprecommits
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact transfer hprecommits
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with ⟨hstepOld, _, hprecommits, _, _⟩
      unfold if_sent_precommit_then_sent_prevote at hold ⊢
      intro r hr m hm hsrc
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · obtain ⟨pv, hpv, hsrcPv⟩ :=
          hold r (by simpa [hMax] using hr) m hm
            (by simpa [hCorr] using hsrc)
        exact ⟨pv, hmono.prevotes r hpv, hsrcPv⟩
      · simp at hm
        subst m
        rcases hprevoteStep p hp hstepOld with ⟨pv, hpv, _, hsrcPv⟩
        exact ⟨pv, by rw [hrEq]; exact hmono.prevotes _ hpv,
          hsrcPv.symm⟩
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact transfer hprecommits

def PrecommitQuorumCondition (s : State) (r : Int)
    (m : VoteMsg) : Prop :=
  m.id ∈ s.ValidValues ∧
      (pv_set s r m.id).card ≥ 2 * s.T + 1 ∨
    m.id = -1 ∧
      (vote_senders s
        (Finmap.lookupD r s.msgs_prevote)).card ≥ 2 * s.T + 1

lemma precommit_quorum_condition_iff
    (s : State) :
    if_sent_precommit_then_received_two_thirds s ↔
      ∀ r ∈ Finset.Icc 0 s.MaxRound,
        ∀ m ∈ Finmap.lookupD r s.msgs_precommit,
          m.src ∈ s.Corr → PrecommitQuorumCondition s r m := by
  unfold if_sent_precommit_then_received_two_thirds
  constructor
  · intro h r hr m hm hsrc
    rcases h r hr m hm hsrc with hgood | hnil
    · left
      exact ⟨hgood.1, by
        simpa [PrecommitQuorumCondition, pv_set, vote_senders,
          votes_for, all_replicas, eq_comm] using hgood.2⟩
    · right
      exact ⟨hnil.1, by
        simpa [PrecommitQuorumCondition, vote_senders,
          all_replicas, eq_comm] using hnil.2⟩
  · intro h r hr m hm hsrc
    rcases h r hr m hm hsrc with hgood | hnil
    · left
      exact ⟨hgood.1, by
        simpa [PrecommitQuorumCondition, pv_set, vote_senders,
          votes_for, all_replicas, eq_comm] using hgood.2⟩
    · right
      exact ⟨hnil.1, by
        simpa [PrecommitQuorumCondition, vote_senders,
          all_replicas, eq_comm] using hnil.2⟩

set_option maxHeartbeats 300000 in
lemma precommit_quorum_transfer_raw {s s' : State}
    (hold : if_sent_precommit_then_received_two_thirds s)
    (hnext : Next s s') {r : Int} {m : VoteMsg}
    (hr : r ∈ Finset.Icc 0 s'.MaxRound)
    (hm : m ∈ Finmap.lookupD r s.msgs_precommit)
    (hsrc : m.src ∈ s'.Corr) :
    PrecommitQuorumCondition s' r m := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, hValid, _, hMax, _⟩
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have hsrcOld : m.src ∈ s.Corr := by simpa [hCorr] using hsrc
  rcases hold r hrOld m hm hsrcOld with hgood | hnil
  · left
    refine ⟨by simpa [hValid] using hgood.1, ?_⟩
    have hcardOld : (pv_set s r m.id).card ≥ 2 * s.T + 1 := by
      simpa [pv_set, vote_senders, votes_for, all_replicas,
        eq_comm] using hgood.2
    have hsub := pv_set_mono_frame hCorr hFaulty
      (hmono.prevotes r) (v := m.id)
    have hcardLe := Finset.card_le_card hsub
    have hcardNew : (pv_set s' r m.id).card ≥ 2 * s'.T + 1 := by omega
    exact hcardNew
  · right
    refine ⟨hnil.1, ?_⟩
    have hcardOld :
        (vote_senders s (Finmap.lookupD r s.msgs_prevote)).card ≥
          2 * s.T + 1 := by
      simpa [vote_senders, all_replicas, eq_comm] using hnil.2
    have hsub := vote_senders_mono_frame hCorr hFaulty
      (hmono.prevotes r)
    have hcardLe := Finset.card_le_card hsub
    have hcardNew :
        (vote_senders s'
          (Finmap.lookupD r s'.msgs_prevote)).card ≥
            2 * s'.T + 1 := by omega
    exact hcardNew

set_option maxHeartbeats 300000 in
lemma next_preserves_precommit_quorum {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hold : if_sent_precommit_then_received_two_thirds s)
    (hnext : Next s s') :
    if_sent_precommit_then_received_two_thirds s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, hValid, _, hMax, _⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have transferAt {r : Int} {m : VoteMsg}
      (hr : r ∈ Finset.Icc 0 s.MaxRound)
      (hm : m ∈ Finmap.lookupD r s.msgs_precommit)
      (hsrc : m.src ∈ s.Corr) :
      m.id ∈ s'.ValidValues ∧
            (pv_set s' r m.id).card ≥ 2 * s'.T + 1 ∨
        m.id = -1 ∧
            (vote_senders s'
              (Finmap.lookupD r s'.msgs_prevote)).card ≥
                2 * s'.T + 1 := by
    rcases hold r hr m hm hsrc with hgood | hnil
    · left
      refine ⟨by simpa [hValid] using hgood.1, ?_⟩
      have hcardOld : (pv_set s r m.id).card ≥ 2 * s.T + 1 := by
        simpa [pv_set, vote_senders, votes_for, all_replicas,
          eq_comm] using hgood.2
      have hsub := pv_set_mono_frame hCorr hFaulty
        (hmono.prevotes r) (v := m.id)
      have := Finset.card_le_card hsub
      omega
    · right
      refine ⟨hnil.1, ?_⟩
      have hcardOld :
          (vote_senders s
            (Finmap.lookupD r s.msgs_prevote)).card ≥
              2 * s.T + 1 := by
        simpa [vote_senders, all_replicas, eq_comm] using hnil.2
      have hsub := vote_senders_mono_frame hCorr hFaulty
        (hmono.prevotes r)
      have := Finset.card_le_card hsub
      omega
  have hnextCopy := hnext
  rw [precommit_quorum_condition_iff]
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, ⟨r₀, hr₀, hrest⟩, hCorrEq, hFaultyEq, _, _, _, _,
      hMaxEq, _⟩ := hfaulty
    obtain ⟨_, _, _, _, _, hblock⟩ := hrest
    obtain ⟨fps, hfps, _, value, hvalue, hprecommits⟩ := hblock
    intro r hr m hm hsrc
    rw [hprecommits, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m
        hr hm hsrc
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hsrcFaulty : src ∈ s.Faulty :=
        Finset.mem_powerset.mp hfps hsrcFps
      have hsrcCorr : src ∈ s.Corr := by simpa [hCorrEq] using hsrc
      have hboth : src ∈ s.Corr ∩ s.Faulty := by
        simp [hsrcCorr, hsrcFaulty]
      simpa [hmodel.2.2.2.1] using hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hprevotes⟩
      rcases hact with
        ⟨_, _, evidence, hevidence, hcard, hprecommits, _, _⟩
      intro r hr m hm hsrc
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m
          hr hm hsrc
      · simp at hm
        subst m
        right
        refine ⟨rfl, ?_⟩
        let senders := vote_senders s evidence
        have hevidenceSub :
            evidence ⊆
              Finmap.lookupD (Finmap.lookupD p s.round)
                s.msgs_prevote :=
          Finset.mem_powerset.mp hevidence
        have hsenderSub :
            senders ⊆
              vote_senders s'
                (Finmap.lookupD (Finmap.lookupD p s.round)
                  s'.msgs_prevote) :=
          vote_senders_mono_frame hCorr hFaulty
            (fun _ hm => hmono.prevotes _ (hevidenceSub hm))
        have hcardSenders : (senders.card : Int) ≥ 2 * s.T + 1 := by
          simpa [senders, vote_senders, all_replicas, eq_comm] using hcard
        have hcardLe := Finset.card_le_card hsenderSub
        have hcardNew :
            ((vote_senders s'
              (Finmap.lookupD (Finmap.lookupD p s.round)
                s'.msgs_prevote)).card : Int) ≥ 2 * s'.T + 1 := by omega
        simpa [PrecommitQuorumCondition, hrEq] using hcardNew
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, hprevotes⟩
      rcases hact with
        ⟨_, _, value, hvalue, _, _, _, _, hquorum, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with ⟨_, _, _, hprecommits, _⟩
        intro r hr m hm hsrc
        rw [hprecommits, mem_lookupD_insert_union_iff] at hm
        rcases hm with hm | ⟨hrEq, hm⟩
        · exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m
            hr hm hsrc
        · simp at hm
          subst m
          left
          refine ⟨by simpa [hValid] using hvalue, ?_⟩
          have hrange := ht.round_values p hp
          have hcardOld :
              (pv_set s (Finmap.lookupD p s.round) value).card ≥
                2 * s.T + 1 := by
            rw [← prevote_value_messages_card_eq_pv_set htype hrange]
            exact hquorum
          have hsub := pv_set_mono_frame hCorr hFaulty
            (hmono.prevotes (Finmap.lookupD p s.round)) (v := value)
          have hcardLe := Finset.card_le_card hsub
          have hcardNew :
              ((pv_set s' (Finmap.lookupD p s.round) value).card : Int) ≥
                2 * s'.T + 1 := by omega
          simpa [hrEq] using hcardNew
      · rcases hstay with ⟨_, _, _, hprecommits, _⟩
        intro r hr m hm hsrc
        exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
          (by simpa [hprecommits] using hm) hsrc
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
          hprevotes⟩
      rcases hact with
        ⟨_, hquorum, hprecommits, _, _⟩
      intro r hr m hm hsrc
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m
          hr hm hsrc
      · simp at hm
        subst m
        right
        refine ⟨rfl, ?_⟩
        have hrange := ht.round_values p hp
        have hnilCard :
            (pv_set s (Finmap.lookupD p s.round) (-1)).card ≥
              2 * s.T + 1 := by
          rw [← prevote_value_messages_card_eq_pv_set htype hrange]
          simpa [eq_comm] using hquorum
        have hsub₁ := pv_set_mono_frame hCorr hFaulty
          (hmono.prevotes (Finmap.lookupD p s.round)) (v := -1)
        have hsub₂ :
            pv_set s' (Finmap.lookupD p s.round) (-1) ⊆
              vote_senders s'
                (Finmap.lookupD (Finmap.lookupD p s.round)
                  s'.msgs_prevote) := by
          intro src hsrc
          rcases (mem_pv_set.mp hsrc) with
            ⟨hall, pv, hpv, hid, hsrcPv⟩
          exact Finset.mem_filter.mpr ⟨hall, pv, hpv, hsrcPv⟩
        have hcardLe₁ := Finset.card_le_card hsub₁
        have hcardLe₂ := Finset.card_le_card hsub₂
        have hcardNew :
            ((vote_senders s'
              (Finmap.lookupD (Finmap.lookupD p s.round)
                s'.msgs_prevote)).card : Int) ≥ 2 * s'.T + 1 := by omega
        simpa [PrecommitQuorumCondition, hrEq] using hcardNew
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      intro r hr m hm hsrc
      exact @precommit_quorum_transfer_raw s s' hold hnextCopy r m hr
        (by simpa [hprecommits] using hm) hsrc

lemma next_preserves_latest_precommit {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hold : all_latest_precommit_has_locked_round s)
    (hnext : Next s s') :
    all_latest_precommit_has_locked_round s' := by
  have hmono := next_messages_monotone hnext
  have htype' := next_preserves_ind_type_ok htype hnext
  have ht := (ind_type_ok_iff_components s).mp htype
  have ht' := (ind_type_ok_iff_components s').mp htype'
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, _, _, _, hMax, _⟩
  have hdisjoint := hmodel.2.2.2.1
  unfold all_latest_precommit_has_locked_round at hold ⊢
  intro q hq'
  have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
  have preserveFrame
      (hLR :
        Finmap.lookupD q s'.locked_round =
          Finmap.lookupD q s.locked_round)
      (hLV :
        Finmap.lookupD q s'.locked_value =
          Finmap.lookupD q s.locked_value) :
      (Finmap.lookupD q s'.locked_round = -1 ∧
          Finmap.lookupD q s'.locked_value = -1 ∧
            ∀ r ∈ Finset.Icc 0 s'.MaxRound,
              ∀ m ∈ Finmap.lookupD r s'.msgs_precommit,
                q ≠ m.src ∨ m.id = -1) ∨
        Finmap.lookupD q s'.locked_round ≠ -1 ∧
          Finmap.lookupD q s'.locked_value ≠ -1 ∧
            (∀ r ∈ Finset.Icc 0 s'.MaxRound,
                ∀ m ∈ Finmap.lookupD r s'.msgs_precommit,
                  (q ≠ m.src ∨
                    m.round ≤ Finmap.lookupD q s'.locked_round) ∨
                    m.id = -1) ∧
              ∃ m ∈
                  Finmap.lookupD
                    (Finmap.lookupD q s'.locked_round)
                    s'.msgs_precommit,
                q = m.src ∧
                  m.id = Finmap.lookupD q s'.locked_value := by
    rcases hold q hq with hnilOld | hlockedOld
    · left
      refine ⟨by simpa [hLR] using hnilOld.1,
        by simpa [hLV] using hnilOld.2.1, ?_⟩
      intro r hr m hm
      by_cases hsrc : q = m.src
      · right
        by_cases hid : m.id = -1
        · exact hid
        · by_cases hmOld : m ∈ Finmap.lookupD r s.msgs_precommit
          · rcases hnilOld.2.2 r (by simpa [hMax] using hr) m hmOld with
              hne | hnil
            · exact (hne hsrc).elim
            · exact hnil
          · rcases next_fresh_nonnil_precommit_lock hnext hm hmOld hid with
              hfaulty | ⟨hcorr, hlock, _⟩
            · have hsrcCorr : m.src ∈ s.Corr := hsrc ▸ hq
              have hboth : m.src ∈ s.Corr ∩ s.Faulty :=
                Finset.mem_inter.mpr ⟨hsrcCorr, hfaulty⟩
              rw [hdisjoint] at hboth
              simp at hboth
            · have hrNonneg : 0 ≤ r := (Finset.mem_Icc.mp hr).1
              rw [← hsrc] at hlock
              rw [hLR, hnilOld.1] at hlock
              omega
      · exact Or.inl hsrc
    · right
      refine
        ⟨by simpa [hLR] using hlockedOld.1,
          by simpa [hLV] using hlockedOld.2.1, ?_, ?_⟩
      · intro r hr m hm
        by_cases hsrc : q = m.src
        · by_cases hid : m.id = -1
          · exact Or.inr hid
          · left
            right
            by_cases hmOld : m ∈ Finmap.lookupD r s.msgs_precommit
            · rcases hlockedOld.2.2.1 r (by simpa [hMax] using hr)
                  m hmOld with holdBound | holdNil
              · rcases holdBound with hne | hle
                · exact (hne hsrc).elim
                · simpa [hLR] using hle
              · exact (hid holdNil).elim
            · rcases next_fresh_nonnil_precommit_lock hnext hm hmOld hid with
                hfaulty | ⟨hcorr, hlock, _⟩
              · have hsrcCorr : m.src ∈ s.Corr := hsrc ▸ hq
                have hboth : m.src ∈ s.Corr ∩ s.Faulty :=
                  Finset.mem_inter.mpr ⟨hsrcCorr, hfaulty⟩
                rw [hdisjoint] at hboth
                simp at hboth
              · have hrKey : r ∈ Finmap.keys s'.msgs_precommit := by
                  rw [ht'.precommit_keys]
                  exact hr
                have hmRound := ht'.precommits_round r hrKey m hm
                rw [← hsrc] at hlock
                omega
        · exact Or.inl (Or.inl hsrc)
      · rcases hlockedOld.2.2.2 with ⟨m, hm, hsrc, hid⟩
        refine ⟨m, ?_, hsrc, ?_⟩
        · rw [hLR]
          exact hmono.precommits _ hm
        · simpa [hLV] using hid
  rcases next_locked_evolution hnext with
      ⟨hlockedValue, hlockedRound⟩ |
      ⟨p, value, hp, hvalue, hlockedValue, hlockedRound,
        hvalidRound, hsent⟩
  · apply preserveFrame
    · simp [hlockedRound]
    · simp [hlockedValue]
  · by_cases hqp : q = p
    · subst q
      right
      have hvalueNonNil : value ≠ -1 := by
        intro heq
        subst value
        exact hmodel.2.2.2.2.2.2.2.2.1 hvalue
      have hroundNonNil : Finmap.lookupD p s.round ≠ -1 := by
        have hrange := ht.round_values p hp
        have := (Finset.mem_Icc.mp hrange).1
        omega
      refine ⟨by simp [hlockedRound, hroundNonNil],
        by simp [hlockedValue, hvalueNonNil], ?_, ?_⟩
      · intro r hr m hm
        by_cases hsrc : p = m.src
        · by_cases hid : m.id = -1
          · exact Or.inr hid
          · left
            right
            by_cases hmOld : m ∈ Finmap.lookupD r s.msgs_precommit
            · have hle := correct_precommit_round_le_current
                hnofuture hp (by simpa [hMax] using hr) hmOld hsrc
              have hrKey : r ∈ Finmap.keys s.msgs_precommit := by
                rw [ht.precommit_keys]
                simpa [hMax] using hr
              have hmRound := ht.precommits_round r hrKey m hmOld
              simpa [hlockedRound] using (show m.round ≤
                Finmap.lookupD p s.round by omega)
            · rcases next_fresh_nonnil_precommit_lock hnext hm hmOld hid with
                hfaulty | ⟨_, hlock, _⟩
              · have hsrcCorr : m.src ∈ s.Corr := hsrc ▸ hp
                have hboth : m.src ∈ s.Corr ∩ s.Faulty :=
                  Finset.mem_inter.mpr ⟨hsrcCorr, hfaulty⟩
                rw [hdisjoint] at hboth
                simp at hboth
              · have hrKey : r ∈ Finmap.keys s'.msgs_precommit := by
                  rw [ht'.precommit_keys]
                  exact hr
                have hmRound := ht'.precommits_round r hrKey m hm
                rw [← hsrc] at hlock
                omega
        · exact Or.inl (Or.inl hsrc)
      · refine ⟨VoteMsg.mk value VoteKind.PRECOMMIT
          (Finmap.lookupD p s.round) p, ?_, rfl, ?_⟩
        · simpa [hlockedRound] using hsent
        · simp [hlockedValue]
    · apply preserveFrame
      · simp [hlockedRound, lookupD_insert_of_ne hqp]
      · simp [hlockedValue, lookupD_insert_of_ne hqp]

def PrevoteCauseCondition (s : State) (r : Int) (m : VoteMsg) : Prop :=
  m.src ∈ s.Faulty ∨
    m.id = -1 ∨
      m.id ≠ -1 ∧
        ((∃ prop ∈ Finmap.lookupD r s.msgs_propose,
            prop.src = Finmap.lookupD r s.Proposer ∧
              prop.proposal = m.id ∧ prop.valid_round = -1) ∨
          ∃ rr ∈ Finset.filter (fun x => x < r)
              (Finset.Icc 0 s.MaxRound),
            (∃ prop ∈ Finmap.lookupD r s.msgs_propose,
              prop.src = Finmap.lookupD r s.Proposer ∧
                prop.proposal = m.id ∧ rr = prop.valid_round) ∧
              (pv_set s rr m.id).card ≥ 2 * s.T + 1)

lemma prevote_cause_condition_iff (s : State) :
    all_if_sent_prevote_then_received_proposal_or_two_thirds s ↔
      ∀ r ∈ Finset.Icc 0 s.MaxRound,
        ∀ m ∈ Finmap.lookupD r s.msgs_prevote,
          PrevoteCauseCondition s r m := by
  unfold all_if_sent_prevote_then_received_proposal_or_two_thirds
  constructor
  · intro h r hr m hm
    rcases h r hr m hm with hfaulty | hnil | ⟨hnil, hcause⟩
    · exact Or.inl hfaulty
    · exact Or.inr (Or.inl hnil)
    · right; right
      refine ⟨hnil, ?_⟩
      rcases hcause with hproposal | hquorum
      · exact Or.inl hproposal
      · rcases hquorum with ⟨rr, hrr, hproposal, hcard⟩
        right
        refine ⟨rr, hrr, hproposal, ?_⟩
        simpa [pv_set, vote_senders, votes_for, all_replicas,
          eq_comm] using hcard
  · intro h r hr m hm
    rcases h r hr m hm with hfaulty | hnil | ⟨hnil, hcause⟩
    · exact Or.inl hfaulty
    · exact Or.inr (Or.inl hnil)
    · right; right
      refine ⟨hnil, ?_⟩
      rcases hcause with hproposal | hquorum
      · exact Or.inl hproposal
      · rcases hquorum with ⟨rr, hrr, hproposal, hcard⟩
        right
        refine ⟨rr, hrr, hproposal, ?_⟩
        simpa [pv_set, vote_senders, votes_for, all_replicas,
          eq_comm] using hcard

lemma next_preserves_prevote_cause {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hold : all_if_sent_prevote_then_received_proposal_or_two_thirds s)
    (hnext : Next s s') :
    all_if_sent_prevote_then_received_proposal_or_two_thirds s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, hValid, hInvalid, hMax, hProposer⟩
  have ht := (ind_type_ok_iff_components s).mp htype
  have hnextCopy := hnext
  have transferOld {r : Int} {m : VoteMsg}
      (hr : r ∈ Finset.Icc 0 s'.MaxRound)
      (hm : m ∈ Finmap.lookupD r s.msgs_prevote) :
      PrevoteCauseCondition s' r m := by
    have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
      simpa [hMax] using hr
    have hc :=
      (prevote_cause_condition_iff s).mp hold r hrOld m hm
    rcases hc with hfaulty | hnil | ⟨hnil, hcause⟩
    · left
      simpa [hFaulty] using hfaulty
    · right; left; exact hnil
    · right; right
      refine ⟨hnil, ?_⟩
      rcases hcause with hproposal | hquorum
      · left
        rcases hproposal with ⟨prop, hprop, hsrc, hid, hvr⟩
        refine ⟨prop, hmono.proposals r hprop, ?_, hid, hvr⟩
        simpa [hProposer] using hsrc
      · right
        rcases hquorum with ⟨rr, hrr, hproposal, hcard⟩
        have hrr' :
            rr ∈ Finset.filter (fun x => x < r)
              (Finset.Icc 0 s'.MaxRound) := by
          simpa [hMax] using hrr
        refine ⟨rr, hrr', ?_, ?_⟩
        · rcases hproposal with ⟨prop, hprop, hsrc, hid, hvr⟩
          refine ⟨prop, hmono.proposals r hprop, ?_, hid, hvr⟩
          simpa [hProposer] using hsrc
        · have hsub := pv_set_mono_frame hCorr hFaulty
            (hmono.prevotes rr) (v := m.id)
          have hle := Finset.card_le_card hsub
          omega
  rw [prevote_cause_condition_iff]
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _, hFaultyEq, _, _, _, _, hMaxEq, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, _, _, hblock, _⟩ := hrest
    obtain ⟨fps, hfps, _, value, _, hprevotes⟩ := hblock
    intro r hr m hm
    rw [hprevotes, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact transferOld hr hm
    · left
      simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrc, rfl⟩
      simpa [hFaultyEq] using Finset.mem_powerset.mp hfps hsrc
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals, _⟩
      rcases hact with
        ⟨_, _, value, _, hproposal, hprevotes, _, _⟩
      intro r hr m hm
      rw [hprevotes, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · exact transferOld hr hm
      · simp at hm
        subst m
        let condition :=
          value ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round = -1 ∨
              Finmap.lookupD p s.locked_value = value)
        by_cases hc : condition
        · right; right
          have hvalueNonNil : value ≠ -1 := by
            intro heq
            subst value
            exact hmodel.2.2.2.2.2.2.2.2.1 hc.1
          refine ⟨by simpa [condition, hc] using hvalueNonNil, Or.inl ?_⟩
          refine ⟨ProposalMsg.mk value (Finmap.lookupD p s.round)
            (Finmap.lookupD (Finmap.lookupD p s.round) s.Proposer) (-1),
            ?_, ?_, ?_, rfl⟩
          · simpa [hrEq, hproposals] using hproposal
          · simp [hrEq, hProposer]
          · simp [condition, hc]
        · right; left
          simp [condition, hc]
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals, _⟩
      rcases hact with
        ⟨_, _, value, _, _, vr, hvr, _, hvrlt, hproposal, hcard,
          hprevotes, _, _⟩
      intro r hr m hm
      rw [hprevotes, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hrEq, hm⟩
      · exact transferOld hr hm
      · simp at hm
        subst m
        let condition :=
          value ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round ≤ vr ∨
              Finmap.lookupD p s.locked_value = value)
        by_cases hc : condition
        · right; right
          have hvalueNonNil : value ≠ -1 := by
            intro heq
            subst value
            exact hmodel.2.2.2.2.2.2.2.2.1 hc.1
          refine ⟨by simpa [condition, hc] using hvalueNonNil, Or.inr ?_⟩
          have hvrPost :
              vr ∈ Finset.filter (fun x => x < r)
                (Finset.Icc 0 s'.MaxRound) := by
            simp only [Finset.mem_filter]
            refine ⟨by simpa [hMax] using hvr, ?_⟩
            simpa [hrEq] using hvrlt
          refine ⟨vr, hvrPost, ?_, ?_⟩
          · refine ⟨ProposalMsg.mk value (Finmap.lookupD p s.round)
              (Finmap.lookupD (Finmap.lookupD p s.round) s.Proposer) vr,
              ?_, ?_, ?_, rfl⟩
            · simpa [hrEq, hproposals] using hproposal
            · simp [hrEq, hProposer]
            · simp [condition, hc]
          · have hrange : vr ∈ Finset.Icc 0 s.MaxRound := hvr
            have hcardOld : (pv_set s vr value).card ≥ 2 * s.T + 1 := by
              rw [← prevote_value_messages_card_eq_pv_set htype hrange]
              exact hcard
            have hsub := pv_set_mono_frame hCorr hFaulty
              (hmono.prevotes vr) (v := value)
            have hle := Finset.card_le_card hsub
            simpa [condition, hc] using
              (show (pv_set s' vr value).card ≥ 2 * s'.T + 1 by omega)
        · right; left
          simp [condition, hc]
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprevotes⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprevotes, _⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold on_timeout_propose at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _⟩
      rcases hact with ⟨_, _, hprevotes, _, _⟩
      intro r hr m hm
      rw [hprevotes, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact transferOld hr hm
      · simp at hm
        subst m
        exact Or.inr (Or.inl rfl)
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      intro r hr m hm
      exact transferOld hr (by simpa [hprevotes] using hm)

def ProposalNoEquivAt (s : State) (r : Int) : Prop :=
  ∃ value ∈ s.ValidValues,
    ∃ validRound ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅,
      ∀ m ∈ Finmap.lookupD r s.msgs_propose,
        m.src ∈ s.Faulty ∨
          (m.src = Finmap.lookupD r s.Proposer ∧
            value = m.proposal) ∧ validRound = m.valid_round

def PrevoteNoEquivAt (s : State) (r : Int) : Prop :=
  ∀ p ∈ s.Corr,
    ∃ value ∈ s.ValidValues ∪ insert (-1) ∅,
      ∀ m ∈ Finmap.lookupD r s.msgs_prevote,
        p = m.src → value = m.id

def PrecommitNoEquivAt (s : State) (r : Int) : Prop :=
  ∀ p ∈ s.Corr,
    ∃ value ∈ s.ValidValues ∪ insert (-1) ∅,
      ∀ m ∈ Finmap.lookupD r s.msgs_precommit,
        p = m.src → value = m.id

lemma no_equivocation_conditions_iff (s : State) :
    all_no_equivocation_by_correct s ↔
      ∀ r ∈ Finset.Icc 0 s.MaxRound,
        ProposalNoEquivAt s r ∧
          PrevoteNoEquivAt s r ∧ PrecommitNoEquivAt s r := by
  rfl

lemma no_equivocation_frame {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    (hproposals : s'.msgs_propose = s.msgs_propose)
    (hprevotes : s'.msgs_prevote = s.msgs_prevote)
    (hprecommits : s'.msgs_precommit = s.msgs_precommit) :
    all_no_equivocation_by_correct s' := by
  rcases hparams with
    ⟨hCorr, hFaulty, _, _, hValid, _, hMax, hProposer⟩
  rw [no_equivocation_conditions_iff]
  intro r hr
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  rcases (no_equivocation_conditions_iff s).mp hold r hrOld with
    ⟨hprop, hpv, hpc⟩
  constructor
  · rcases hprop with ⟨value, hvalue, vr, hvr, hmessages⟩
    refine ⟨value, by simpa [hValid] using hvalue,
      vr, by simpa [hMax] using hvr, ?_⟩
    intro m hm
    rcases hmessages m (by simpa [hproposals] using hm) with
      hfaulty | hcorrect
    · exact Or.inl (by simpa [hFaulty] using hfaulty)
    · right
      simpa [hProposer] using hcorrect
  · constructor
    · intro q hq
      have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
      rcases hpv q hqOld with ⟨value, hvalue, hmessages⟩
      refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
      intro m hm hsrc
      exact hmessages m (by simpa [hprevotes] using hm) hsrc
    · intro q hq
      have hqOld : q ∈ s.Corr := by simpa [hCorr] using hq
      rcases hpc q hqOld with ⟨value, hvalue, hmessages⟩
      refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
      intro m hm hsrc
      exact hmessages m (by simpa [hprecommits] using hm) hsrc

lemma proposal_no_equiv_frame {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    (hmsgs : s'.msgs_propose = s.msgs_propose) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, ProposalNoEquivAt s' r := by
  rcases hparams with
    ⟨_, hFaulty, _, _, hValid, _, hMax, hProposer⟩
  intro r hr
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  rcases ((no_equivocation_conditions_iff s).mp hold r hrOld).1 with
    ⟨value, hvalue, vr, hvr, hmessages⟩
  refine ⟨value, by simpa [hValid] using hvalue,
    vr, by simpa [hMax] using hvr, ?_⟩
  intro m hm
  rcases hmessages m (by simpa [hmsgs] using hm) with
    hfaulty | hcorrect
  · exact Or.inl (by simpa [hFaulty] using hfaulty)
  · exact Or.inr (by simpa [hProposer] using hcorrect)

lemma prevote_no_equiv_frame {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    (hmsgs : s'.msgs_prevote = s.msgs_prevote) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, PrevoteNoEquivAt s' r := by
  rcases hparams with
    ⟨hCorr, _, _, _, hValid, _, hMax, _⟩
  intro r hr q hq'
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
  rcases ((no_equivocation_conditions_iff s).mp hold r hrOld).2.1 q hq with
    ⟨value, hvalue, hmessages⟩
  refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
  intro m hm hsrc
  exact hmessages m (by simpa [hmsgs] using hm) hsrc

lemma precommit_no_equiv_frame {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    (hmsgs : s'.msgs_precommit = s.msgs_precommit) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, PrecommitNoEquivAt s' r := by
  rcases hparams with
    ⟨hCorr, _, _, _, hValid, _, hMax, _⟩
  intro r hr q hq'
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
  rcases ((no_equivocation_conditions_iff s).mp hold r hrOld).2.2 q hq with
    ⟨value, hvalue, hmessages⟩
  refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
  intro m hm hsrc
  exact hmessages m (by simpa [hmsgs] using hm) hsrc

lemma proposal_no_equiv_append {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    {p r₀ value validRound : Int}
    (hvalue : value ∈ s.ValidValues)
    (hvalidRound :
      validRound ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅)
    (hproposer : p = Finmap.lookupD r₀ s.Proposer)
    (hnone : ∀ m ∈ Finmap.lookupD r₀ s.msgs_propose, p ≠ m.src)
    (hmsgs :
      s'.msgs_propose =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_propose ∪
            insert (ProposalMsg.mk value r₀ p validRound) ∅)
          s.msgs_propose) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, ProposalNoEquivAt s' r := by
  rcases hparams with
    ⟨_, hFaulty, _, _, hValid, _, hMax, hProposer⟩
  intro r hr
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have holdAt :=
    ((no_equivocation_conditions_iff s).mp hold r hrOld).1
  by_cases hre : r = r₀
  · subst r
    refine ⟨value, by simpa [hValid] using hvalue,
      validRound, by simpa [hMax] using hvalidRound, ?_⟩
    intro m hm
    rw [hmsgs, lookupD_insert_self] at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases holdAt with ⟨oldValue, _, oldVR, _, holdMessages⟩
      rcases holdMessages m hm with hfaulty | hcorrect
      · exact Or.inl (by simpa [hFaulty] using hfaulty)
      · have hpSrc : p = m.src := by
          rw [hproposer, hcorrect.1.1]
        exact (hnone m hm hpSrc).elim
    · simp at hm
      subst m
      right
      simp [hproposer, hProposer]
  · rcases holdAt with ⟨oldValue, holdValue, oldVR, holdVR, holdMessages⟩
    refine ⟨oldValue, by simpa [hValid] using holdValue,
      oldVR, by simpa [hMax] using holdVR, ?_⟩
    intro m hm
    rw [hmsgs, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨heq, _⟩
    · rcases holdMessages m hm with hfaulty | hcorrect
      · exact Or.inl (by simpa [hFaulty] using hfaulty)
      · exact Or.inr (by simpa [hProposer] using hcorrect)
    · exact (hre heq).elim

lemma prevote_no_equiv_append {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    {p r₀ value : Int}
    (hvalue : value ∈ s.ValidValues ∪ insert (-1) ∅)
    (hnone : ∀ m ∈ Finmap.lookupD r₀ s.msgs_prevote, p ≠ m.src)
    (hmsgs :
      s'.msgs_prevote =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_prevote ∪
            insert (VoteMsg.mk value VoteKind.PREVOTE r₀ p) ∅)
          s.msgs_prevote) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, PrevoteNoEquivAt s' r := by
  rcases hparams with
    ⟨hCorr, _, _, _, hValid, _, hMax, _⟩
  intro r hr q hq'
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
  have holdAt :=
    ((no_equivocation_conditions_iff s).mp hold r hrOld).2.1 q hq
  by_cases hcase : q = p ∧ r = r₀
  · rcases hcase with ⟨rfl, rfl⟩
    refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
    intro m hm hsrc
    rw [hmsgs, lookupD_insert_self] at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact (hnone m hm hsrc).elim
    · simp at hm
      subst m
      rfl
  · rcases holdAt with ⟨oldValue, holdValue, holdMessages⟩
    refine ⟨oldValue, by simpa [hValid] using holdValue, ?_⟩
    intro m hm hsrc
    rw [hmsgs, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨hre, hm⟩
    · exact holdMessages m hm hsrc
    · simp at hm
      subst m
      exact (hcase ⟨hsrc, hre⟩).elim

lemma precommit_no_equiv_append {s s' : State}
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    {p r₀ value : Int}
    (hvalue : value ∈ s.ValidValues ∪ insert (-1) ∅)
    (hnone : ∀ m ∈ Finmap.lookupD r₀ s.msgs_precommit, p ≠ m.src)
    (hmsgs :
      s'.msgs_precommit =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_precommit ∪
            insert (VoteMsg.mk value VoteKind.PRECOMMIT r₀ p) ∅)
          s.msgs_precommit) :
    ∀ r ∈ Finset.Icc 0 s'.MaxRound, PrecommitNoEquivAt s' r := by
  rcases hparams with
    ⟨hCorr, _, _, _, hValid, _, hMax, _⟩
  intro r hr q hq'
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
  have holdAt :=
    ((no_equivocation_conditions_iff s).mp hold r hrOld).2.2 q hq
  by_cases hcase : q = p ∧ r = r₀
  · rcases hcase with ⟨rfl, rfl⟩
    refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
    intro m hm hsrc
    rw [hmsgs, lookupD_insert_self] at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact (hnone m hm hsrc).elim
    · simp at hm
      subst m
      rfl
  · rcases holdAt with ⟨oldValue, holdValue, holdMessages⟩
    refine ⟨oldValue, by simpa [hValid] using holdValue, ?_⟩
    intro m hm hsrc
    rw [hmsgs, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨hre, hm⟩
    · exact holdMessages m hm hsrc
    · simp at hm
      subst m
      exact (hcase ⟨hsrc, hre⟩).elim

lemma no_equivocation_faulty_append {s s' : State}
    (hmodel : model_assumptions s)
    (hold : all_no_equivocation_by_correct s)
    (hparams : same_parameters s s')
    {r₀ value₁ validRound value₂ value₃ : Int}
    {fps₁ fps₂ fps₃ : Finset Int}
    (hfps₁ : fps₁ ⊆ s.Faulty)
    (hfps₂ : fps₂ ⊆ s.Faulty)
    (hfps₃ : fps₃ ⊆ s.Faulty)
    (hproposals :
      s'.msgs_propose =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_propose ∪
            Finset.image
              (fun src => ProposalMsg.mk value₁ r₀ src validRound) fps₁)
          s.msgs_propose)
    (hprevotes :
      s'.msgs_prevote =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_prevote ∪
            Finset.image
              (fun src => VoteMsg.mk value₂ VoteKind.PREVOTE r₀ src) fps₂)
          s.msgs_prevote)
    (hprecommits :
      s'.msgs_precommit =
        Finmap.insert r₀
          (Finmap.lookupD r₀ s.msgs_precommit ∪
            Finset.image
              (fun src =>
                VoteMsg.mk value₃ VoteKind.PRECOMMIT r₀ src) fps₃)
          s.msgs_precommit) :
    all_no_equivocation_by_correct s' := by
  rcases hparams with
    ⟨hCorr, hFaulty, _, _, hValid, _, hMax, hProposer⟩
  have hdisjoint := hmodel.2.2.2.1
  rw [no_equivocation_conditions_iff]
  intro r hr
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by simpa [hMax] using hr
  rcases (no_equivocation_conditions_iff s).mp hold r hrOld with
    ⟨hprop, hpv, hpc⟩
  constructor
  · rcases hprop with ⟨value, hvalue, vr, hvr, hmessages⟩
    refine ⟨value, by simpa [hValid] using hvalue,
      vr, by simpa [hMax] using hvr, ?_⟩
    intro m hm
    rw [hproposals, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · rcases hmessages m hm with hfaulty | hcorrect
      · exact Or.inl (by simpa [hFaulty] using hfaulty)
      · exact Or.inr (by simpa [hProposer] using hcorrect)
    · left
      simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrc, rfl⟩
      simpa [hFaulty] using hfps₁ hsrc
  · constructor
    · intro q hq'
      have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
      rcases hpv q hq with ⟨value, hvalue, hmessages⟩
      refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
      intro m hm hsrc
      rw [hprevotes, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact hmessages m hm hsrc
      · simp only [Finset.mem_image] at hm
        rcases hm with ⟨src, hsrcFps, rfl⟩
        have hboth : q ∈ s.Corr ∩ s.Faulty :=
          Finset.mem_inter.mpr ⟨hq, hsrc ▸ hfps₂ hsrcFps⟩
        rw [hdisjoint] at hboth
        simp at hboth
    · intro q hq'
      have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
      rcases hpc q hq with ⟨value, hvalue, hmessages⟩
      refine ⟨value, by simpa [hValid] using hvalue, ?_⟩
      intro m hm hsrc
      rw [hprecommits, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨_, hm⟩
      · exact hmessages m hm hsrc
      · simp only [Finset.mem_image] at hm
        rcases hm with ⟨src, hsrcFps, rfl⟩
        have hboth : q ∈ s.Corr ∩ s.Faulty :=
          Finset.mem_inter.mpr ⟨hq, hsrc ▸ hfps₃ hsrcFps⟩
        rw [hdisjoint] at hboth
        simp at hboth

lemma next_preserves_no_equivocation {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hold : all_no_equivocation_by_correct s)
    (hnext : Next s s') :
    all_no_equivocation_by_correct s' := by
  have hparams := next_same_parameters hnext
  have ht := (ind_type_ok_iff_components s).mp htype
  have noPrevoteAtPropose {p : Int} (hp : p ∈ s.Corr)
      (hstep : Finmap.lookupD p s.step = Step.PROPOSE) :
      ∀ m ∈ Finmap.lookupD (Finmap.lookupD p s.round) s.msgs_prevote,
        p ≠ m.src := by
    rcases (hnofuture p hp).1.2.1 with h | h | h | h
    · simp_all
    · simp_all
    · simp_all
    · exact h
  have noPrecommitAtPrevote {p : Int} (hp : p ∈ s.Corr)
      (hstep : Finmap.lookupD p s.step = Step.PREVOTE) :
      ∀ m ∈ Finmap.lookupD (Finmap.lookupD p s.round)
          s.msgs_precommit,
        p ≠ m.src := by
    rcases (hnofuture p hp).1.2.2 with h | h | h
    · simp_all
    · simp_all
    · exact h
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, hblock₁, _, hblock₂, _, hblock₃⟩ := hrest
    obtain
      ⟨fps₁, hfps₁, _, value₁, _, _, validRound, _,
        hproposals⟩ := hblock₁
    obtain ⟨fps₂, hfps₂, _, value₂, _, hprevotes⟩ := hblock₂
    obtain ⟨fps₃, hfps₃, _, value₃, _, hprecommits⟩ := hblock₃
    exact no_equivocation_faulty_append hmodel hold hparams
      (Finset.mem_powerset.mp hfps₁)
      (Finset.mem_powerset.mp hfps₂)
      (Finset.mem_powerset.mp hfps₃)
      hproposals hprevotes hprecommits
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hprevotes, hprecommits⟩
      rcases hact with
        ⟨hproposer, _, hnone, _, value, hvalue, hproposals, _⟩
      let newValue :=
        if Finmap.lookupD p s.valid_value ≠ -1
          then Finmap.lookupD p s.valid_value else value
      have hnewValue : newValue ∈ s.ValidValues := by
        dsimp [newValue]
        split
        · rename_i hnonNil
          have hstored := ht.valid_values p hp
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.notMem_empty, or_false] at hstored
          rcases hstored with hvalid | hnil
          · exact hvalid
          · exact (hnonNil hnil).elim
        · exact hvalue
      have hnewVR := ht.valid_rounds p hp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_append hold hparams hnewValue hnewVR
            hproposer hnone (by simpa [newValue] using hproposals) r hr,
          prevote_no_equiv_frame hold hparams hprevotes r hr,
          precommit_no_equiv_frame hold hparams hprecommits r hr⟩
    · unfold upon_proposal_in_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with
        ⟨hstepOld, _, value, _, _, hprevotes, _, _⟩
      let voteValue :=
        if value ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round = -1 ∨
              Finmap.lookupD p s.locked_value = value)
          then value else -1
      have hvote :
          voteValue ∈ s.ValidValues ∪ insert (-1) ∅ := by
        dsimp [voteValue]
        split
        · rename_i hc
          exact Finset.mem_union.mpr (Or.inl hc.1)
        · simp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
          prevote_no_equiv_append hold hparams hvote
            (noPrevoteAtPropose hp hstepOld)
            (by simpa [voteValue] using hprevotes) r hr,
          precommit_no_equiv_frame hold hparams hprecommits r hr⟩
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with
        ⟨hstepOld, _, value, _, _, vr, _, _, _, _, _, hprevotes, _, _⟩
      let voteValue :=
        if value ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round ≤ vr ∨
              Finmap.lookupD p s.locked_value = value)
          then value else -1
      have hvote :
          voteValue ∈ s.ValidValues ∪ insert (-1) ∅ := by
        dsimp [voteValue]
        split
        · rename_i hc
          exact Finset.mem_union.mpr (Or.inl hc.1)
        · simp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
          prevote_no_equiv_append hold hparams hvote
            (noPrevoteAtPropose hp hstepOld)
            (by simpa [voteValue] using hprevotes) r hr,
          precommit_no_equiv_frame hold hparams hprecommits r hr⟩
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprevotes⟩
      rcases hact with
        ⟨hstepOld, _, _, _, _, hprecommits, _, _⟩
      have hnil :
          (-1 : Int) ∈ s.ValidValues ∪ insert (-1) ∅ := by simp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
          prevote_no_equiv_frame hold hparams hprevotes r hr,
          precommit_no_equiv_append hold hparams hnil
            (noPrecommitAtPrevote hp hstepOld) hprecommits r hr⟩
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, hproposals, hprevotes⟩
      rcases hact with
        ⟨_, _, value, hvalue, _, _, _, _, _, hbranch, _, _, _⟩
      rcases hbranch with hsend | hstay
      · rcases hsend with
          ⟨hstepOld, _, _, hprecommits, _⟩
        have hvote :
            value ∈ s.ValidValues ∪ insert (-1) ∅ :=
          Finset.mem_union.mpr (Or.inl hvalue)
        rw [no_equivocation_conditions_iff]
        intro r hr
        refine
          ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
            prevote_no_equiv_frame hold hparams hprevotes r hr,
            precommit_no_equiv_append hold hparams hvote
              (noPrecommitAtPrevote hp hstepOld) hprecommits r hr⟩
      · rcases hstay with ⟨_, _, _, hprecommits, _⟩
        exact no_equivocation_frame hold hparams
          hproposals hprevotes hprecommits
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hproposals,
        hprevotes, hprecommits⟩
      exact no_equivocation_frame hold hparams
        hproposals hprevotes hprecommits
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, hprevotes, hprecommits⟩
      exact no_equivocation_frame hold hparams
        hproposals hprevotes hprecommits
    · unfold on_timeout_propose at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprecommits⟩
      rcases hact with ⟨hstepOld, _, hprevotes, _, _⟩
      have hnil :
          (-1 : Int) ∈ s.ValidValues ∪ insert (-1) ∅ := by simp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
          prevote_no_equiv_append hold hparams hnil
            (noPrevoteAtPropose hp hstepOld) hprevotes r hr,
          precommit_no_equiv_frame hold hparams hprecommits r hr⟩
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hproposals, hprevotes⟩
      rcases hact with ⟨hstepOld, _, hprecommits, _, _⟩
      have hnil :
          (-1 : Int) ∈ s.ValidValues ∪ insert (-1) ∅ := by simp
      rw [no_equivocation_conditions_iff]
      intro r hr
      refine
        ⟨proposal_no_equiv_frame hold hparams hproposals r hr,
          prevote_no_equiv_frame hold hparams hprevotes r hr,
          precommit_no_equiv_append hold hparams hnil
            (noPrecommitAtPrevote hp hstepOld) hprecommits r hr⟩
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, hprevotes, hprecommits⟩
      exact no_equivocation_frame hold hparams
        hproposals hprevotes hprecommits

lemma next_fresh_correct_proposal_shape {s s' : State}
    (hmodel : model_assumptions s) (hnext : Next s s')
    {r : Int} {m : ProposalMsg}
    (hm : m ∈ Finmap.lookupD r s'.msgs_propose)
    (hmOld : m ∉ Finmap.lookupD r s.msgs_propose)
    (hsrc : m.src ∈ s.Corr) :
    r = Finmap.lookupD m.src s.round ∧
      m.valid_round = Finmap.lookupD m.src s.valid_round := by
  have hdisjoint := hmodel.2.2.2.1
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, hblock, _⟩ := hrest
    obtain
      ⟨fps, hfps, _, value, _, _, validRound, _, hproposals⟩ := hblock
    rw [hproposals, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact (hmOld hm).elim
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hboth : src ∈ s.Corr ∩ s.Faulty :=
        Finset.mem_inter.mpr
          ⟨hsrc, Finset.mem_powerset.mp hfps hsrcFps⟩
      rw [hdisjoint] at hboth
      simp at hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with
        ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, _, _, _, value, _, hproposals, _⟩
      rw [hproposals, mem_lookupD_insert_union_iff] at hm
      rcases hm with hm | ⟨hr, hm⟩
      · exact (hmOld hm).elim
      · simp at hm
        subst m
        exact ⟨hr, rfl⟩
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact (hmOld (by simpa [hproposals] using hm)).elim

lemma next_fresh_correct_precommit_proposals_frame {s s' : State}
    (hmodel : model_assumptions s) (hnext : Next s s')
    {r : Int} {m : VoteMsg}
    (hm : m ∈ Finmap.lookupD r s'.msgs_precommit)
    (hmOld : m ∉ Finmap.lookupD r s.msgs_precommit)
    (hsrc : m.src ∈ s.Corr) :
    s'.msgs_propose = s.msgs_propose := by
  have hdisjoint := hmodel.2.2.2.1
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, _, _, _, _, hblock⟩ := hrest
    obtain ⟨fps, hfps, _, value, _, hprecommits⟩ := hblock
    rw [hprecommits, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact (hmOld hm).elim
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hboth : src ∈ s.Corr ∩ s.Faulty :=
        Finset.mem_inter.mpr
          ⟨hsrc, Finset.mem_powerset.mp hfps hsrcFps⟩
      rw [hdisjoint] at hboth
      simp at hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, hprecommits⟩
      exact hproposals
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, hprecommits⟩
      exact hproposals
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact hproposals
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hproposals, _⟩
      exact hproposals
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact hproposals
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact hproposals
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, hprecommits⟩
      exact hproposals
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _⟩
      exact hproposals
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hproposals, _, _⟩
      exact hproposals

lemma next_preserves_locked_proposer_reproposes {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hlatest : all_latest_precommit_has_locked_round s)
    (hbound : all_locked_round_below_valid_round s)
    (hold : all_locked_proposer_reproposes s)
    (hnext : Next s s') :
    all_locked_proposer_reproposes s' := by
  have hmono := next_messages_monotone hnext
  have hsource := next_source_evolution hnext
  have ht := (ind_type_ok_iff_components s).mp htype
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, _, _, _, hMax, hProposer⟩
  have hdisjoint := hmodel.2.2.2.1
  unfold all_locked_proposer_reproposes at hold ⊢
  intro r hr hante r₂ hr₂
  rintro ⟨mm, hmm, hmmsrc, hmmid⟩
  let proposer := Finmap.lookupD r s.Proposer
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
    simpa [hMax] using hr
  have hprCorr : proposer ∈ s.Corr := by
    simpa [proposer, hCorr, hProposer] using hante.1
  rcases hante.2 with ⟨pp, hpp, hppsrc, hppvr⟩
  have hppsrcOld : pp.src = proposer := by
    simpa [proposer, hProposer] using hppsrc
  have hr₂Old : r₂ ∈ Finset.Icc 0 s.MaxRound := by
    simpa [hMax] using (Finset.mem_filter.mp hr₂).1
  have hr₂lt : r₂ < r := (Finset.mem_filter.mp hr₂).2
  have hmmsrcOld : mm.src = proposer := by
    simpa [proposer, hProposer] using hmmsrc
  by_cases hmmOld : mm ∈ Finmap.lookupD r₂ s.msgs_precommit
  · have hlockedNonNil :
        Finmap.lookupD proposer s.locked_round ≠ -1 := by
      rcases hlatest proposer hprCorr with hnil | hlocked
      · rcases hnil.2.2 r₂ hr₂Old mm hmmOld with hne | hid
        · exact (hne hmmsrcOld.symm).elim
        · exact (hmmid hid).elim
      · exact hlocked.1
    by_cases hppOld : pp ∈ Finmap.lookupD r s.msgs_propose
    · have holdAt := hold r hrOld
        ⟨hprCorr, pp, hppOld, by simpa [proposer] using hppsrcOld,
          hppvr⟩
      exact holdAt r₂ (by simpa [hMax] using hr₂)
        ⟨mm, hmmOld, by simpa [proposer] using hmmsrcOld, hmmid⟩
    · have hshape := next_fresh_correct_proposal_shape
        hmodel hnext hpp hppOld
          (by simpa [hppsrcOld] using hprCorr)
      have hvalidNil :
          Finmap.lookupD proposer s.valid_round = -1 := by
        calc
          Finmap.lookupD proposer s.valid_round =
              Finmap.lookupD pp.src s.valid_round := by rw [hppsrcOld]
          _ = pp.valid_round := hshape.2.symm
          _ = -1 := hppvr
      have hle := hbound proposer hprCorr
      have hlrType := ht.locked_rounds proposer hprCorr
      simp only [Finset.mem_union, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hlrType
      rcases hlrType with hlrRange | hlrNil
      · have hlrNonneg := (Finset.mem_Icc.mp hlrRange).1
        omega
      · exact (hlockedNonNil hlrNil).elim
  · have hroundEq : r₂ = Finmap.lookupD proposer s.round := by
      rcases hsource.precommits r₂ mm hmm with
        holdMsg | hfaulty | ⟨hcorr, hround, _⟩
      · exact (hmmOld holdMsg).elim
      · have hboth : proposer ∈ s.Corr ∩ s.Faulty := by
          apply Finset.mem_inter.mpr
          exact ⟨hprCorr, by simpa [hmmsrcOld] using hfaulty⟩
        rw [hdisjoint] at hboth
        simp at hboth
      · simpa [hmmsrcOld] using hround
    have hproposals :=
      next_fresh_correct_precommit_proposals_frame
        hmodel hnext hmm hmmOld
          (by simpa [hmmsrcOld] using hprCorr)
    have hppOld : pp ∈ Finmap.lookupD r s.msgs_propose := by
      simpa [hproposals] using hpp
    have hrFuture :
        r ∈ Finset.filter
          (fun x => x > Finmap.lookupD proposer s.round)
          (Finset.Icc 0 s.MaxRound) := by
      exact Finset.mem_filter.mpr ⟨hrOld, by omega⟩
    have hne :=
      (hnofuture proposer hprCorr).2 r hrFuture |>.1 pp hppOld
    exact hne hppsrcOld.symm

def proposal_senders (s : State) (msgs : Finset ProposalMsg) :
    Finset Int :=
  Finset.filter (fun p => ∃ m ∈ msgs, p = m.src) (all_replicas s)

def pv_all (s : State) (r : Int) : Finset Int :=
  vote_senders s (Finmap.lookupD r s.msgs_prevote)

def pc_all (s : State) (r : Int) : Finset Int :=
  vote_senders s (Finmap.lookupD r s.msgs_precommit)

def past_start_quorum (s : State) (r : Int) : Prop :=
  (pv_all s r ∪ pc_all s r).card ≥ s.T + 1 ∨
    (pc_all s (r - 1)).card ≥ 2 * s.T + 1

lemma past_start_round_condition_iff (s : State) :
    all_past_start_round s ↔
      ∀ p ∈ s.Corr,
        ∀ r ∈ Finset.Icc 0 s.MaxRound,
          r > Finmap.lookupD p s.round ∨
            r = 0 ∨ past_start_quorum s r := by
  unfold all_past_start_round past_start_quorum
  constructor
  · intro h p hp r hr
    rcases h p hp r hr with hfuture | hzero | hq₁ | hq₂
    · exact Or.inl hfuture
    · exact Or.inr (Or.inl hzero)
    · right; right; left
      simpa [vote_senders, all_replicas, eq_comm] using hq₁
    · right; right; right
      convert hq₂ using 1
      congr 2
      ext x
      simp [pc_all, vote_senders, all_replicas, eq_comm]
  · intro h p hp r hr
    rcases h p hp r hr with hfuture | hzero | hq₁ | hq₂
    · exact Or.inl hfuture
    · exact Or.inr (Or.inl hzero)
    · right; right; left
      simpa [vote_senders, all_replicas, eq_comm] using hq₁
    · right; right; right
      convert hq₂ using 1 <;>
        congr 2 <;>
          ext x <;>
            simp [pc_all, vote_senders, all_replicas, eq_comm]

lemma proposal_senders_subset (s : State) (msgs : Finset ProposalMsg) :
    proposal_senders s msgs ⊆ all_replicas s := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma proposal_senders_mono_frame {s s' : State}
    {msgs msgs' : Finset ProposalMsg}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hsub : msgs ⊆ msgs') :
    proposal_senders s msgs ⊆ proposal_senders s' msgs' := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hall, m, hm, hsrc⟩
  exact Finset.mem_filter.mpr
    ⟨by simpa [all_replicas, hCorr, hFaulty] using hall,
      m, hsub hm, hsrc⟩

lemma threshold_has_correct {s : State}
    (hmodel : model_assumptions s) {A : Finset Int}
    (hsub : A ⊆ all_replicas s)
    (hcard : (A.card : Int) ≥ s.T + 1) :
    ∃ c ∈ s.Corr, c ∈ A := by
  by_contra hnone
  push_neg at hnone
  have hAFaulty : A ⊆ s.Faulty := by
    intro x hx
    rcases Finset.mem_union.mp (hsub hx) with hcorr | hfaulty
    · exact (hnone x hcorr hx).elim
    · exact hfaulty
  have hle := Finset.card_le_card hAFaulty
  have hfault := hmodel.2.2.1
  omega

inductive RoundEvolution (s s' : State) : Prop where
  | frame (hround : s'.round = s.round)
  | advance (p : Int) (hp : p ∈ s.Corr)
      (evidence : Finset VoteMsg)
      (hevidence :
        evidence ⊆
          Finmap.lookupD (Finmap.lookupD p s.round) s.msgs_precommit)
      (hcard : (vote_senders s evidence).card ≥ 2 * s.T + 1)
      (hround :
        s'.round =
          Finmap.insert p (Finmap.lookupD p s.round + 1) s.round)
  | catchup (p rnd : Int) (hp : p ∈ s.Corr)
      (hrnd : rnd ∈ Finset.Icc 0 s.MaxRound)
      (evProposal : Finset ProposalMsg)
      (evPrevote evPrecommit : Finset VoteMsg)
      (hProposal :
        evProposal ⊆ Finmap.lookupD rnd s.msgs_propose)
      (hPrevote :
        evPrevote ⊆ Finmap.lookupD rnd s.msgs_prevote)
      (hPrecommit :
        evPrecommit ⊆ Finmap.lookupD rnd s.msgs_precommit)
      (hcard :
        (proposal_senders s evProposal ∪
          vote_senders s evPrevote ∪
            vote_senders s evPrecommit).card ≥ s.T + 1)
      (hround : s'.round = Finmap.insert p rnd s.round)

lemma next_round_evolution {s s' : State} (hnext : Next s s') :
    RoundEvolution s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with ⟨_, _, _, _, _, _, _, _, _, _, hround, _⟩
    exact .frame hround
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨_, evidence, hevidence, hcard, _, _, hround, _, _⟩
      apply RoundEvolution.advance p hp evidence
        (Finset.mem_powerset.mp hevidence) ?_ hround
      simpa [vote_senders, all_replicas, eq_comm] using hcard
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, hround, _⟩
      exact .frame hround
    · unfold on_round_catchup at h
      rcases h with ⟨_, hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
      rcases hact with
        ⟨rnd, hrnd, _, evProposal, hProposal, _, evPrevote, hPrevote,
          _, evPrecommit, hPrecommit, _, hcard, _, hround, _, _⟩
      apply RoundEvolution.catchup p rnd hp hrnd evProposal evPrevote
        evPrecommit (Finset.mem_powerset.mp hProposal)
        (Finset.mem_powerset.mp hPrevote)
        (Finset.mem_powerset.mp hPrecommit) ?_ hround
      simpa [proposal_senders, vote_senders, all_replicas, eq_comm,
        Finset.union_assoc] using hcard

lemma pv_all_mono_frame {s s' : State} {r : Int}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hmsgs :
      Finmap.lookupD r s.msgs_prevote ⊆
        Finmap.lookupD r s'.msgs_prevote) :
    pv_all s r ⊆ pv_all s' r := by
  exact vote_senders_mono_frame hCorr hFaulty hmsgs

lemma pc_all_mono_frame {s s' : State} {r : Int}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hmsgs :
      Finmap.lookupD r s.msgs_precommit ⊆
        Finmap.lookupD r s'.msgs_precommit) :
    pc_all s r ⊆ pc_all s' r := by
  exact vote_senders_mono_frame hCorr hFaulty hmsgs

lemma past_start_quorum_mono {s s' : State} {r : Int}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hT : s'.T = s.T) (hmono : MessagesMonotone s s')
    (hq : past_start_quorum s r) :
    past_start_quorum s' r := by
  rcases hq with hq | hq
  · left
    have hsub :
        pv_all s r ∪ pc_all s r ⊆
          pv_all s' r ∪ pc_all s' r :=
      Finset.union_subset
        (Finset.Subset.trans
          (pv_all_mono_frame hCorr hFaulty (hmono.prevotes r))
          Finset.subset_union_left)
        (Finset.Subset.trans
          (pc_all_mono_frame hCorr hFaulty (hmono.precommits r))
          Finset.subset_union_right)
    have hle := Finset.card_le_card hsub
    omega
  · right
    have hsub := pc_all_mono_frame hCorr hFaulty
      (hmono.precommits (r - 1))
    have hle := Finset.card_le_card hsub
    omega

lemma next_preserves_past_start_round {s s' : State}
    (hmodel : model_assumptions s)
    (hnofuture : all_no_future_messages_sent s)
    (hold : all_past_start_round s)
    (hnext : Next s s') :
    all_past_start_round s' := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, _, _, hMax, _⟩
  have transferQuorum {r : Int} (hq : past_start_quorum s r) :
      past_start_quorum s' r :=
    past_start_quorum_mono hCorr hFaulty hT hmono hq
  have fromCorrect {c r limit : Int}
      (hc : c ∈ s.Corr)
      (hlimit : limit ≤ Finmap.lookupD c s.round)
      (hr : r ∈ Finset.Icc 0 s'.MaxRound)
      (hrle : r ≤ limit) (hrne : r ≠ 0) :
      past_start_quorum s' r := by
    have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
      simpa [hMax] using hr
    rcases (past_start_round_condition_iff s).mp hold c hc r hrOld with
      hfuture | hzero | hq
    · omega
    · exact (hrne hzero).elim
    · exact transferQuorum hq
  rw [past_start_round_condition_iff]
  rcases next_round_evolution hnext with
      ⟨hround⟩ |
      ⟨p, hp, evidence, hevidence, hcard, hround⟩ |
      ⟨p, rnd, hp, hrnd, evProposal, evPrevote, evPrecommit,
        hProposal, hPrevote, hPrecommit, hcard, hround⟩
  · intro q hq' r hr
    have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
    have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
      simpa [hMax] using hr
    rcases (past_start_round_condition_iff s).mp hold q hq r hrOld with
      hfuture | hzero | hquorum
    · left
      simpa [hround] using hfuture
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr (transferQuorum hquorum))
  · intro q hq' r hr
    have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
    by_cases hqp : q = p
    · subst q
      have hroundPost :
          Finmap.lookupD p s'.round =
            Finmap.lookupD p s.round + 1 := by
        simp [hround]
      by_cases hfuture :
          r > Finmap.lookupD p s'.round
      · exact Or.inl hfuture
      · by_cases hzero : r = 0
        · exact Or.inr (Or.inl hzero)
        · right; right
          by_cases hrle : r ≤ Finmap.lookupD p s.round
          · exact fromCorrect hp (le_refl _) hr hrle hzero
          · have hre : r = Finmap.lookupD p s.round + 1 := by omega
            right
            have hsub :
                vote_senders s evidence ⊆
                  pc_all s' (r - 1) := by
              intro src hsrc
              rcases Finset.mem_filter.mp hsrc with
                ⟨hall, m, hm, hsrcm⟩
              apply Finset.mem_filter.mpr
              refine
                ⟨by simpa [all_replicas, hCorr, hFaulty] using hall,
                  m, ?_, hsrcm⟩
              simpa [pc_all, hre] using
                hmono.precommits (Finmap.lookupD p s.round)
                  (hevidence hm)
            have hle := Finset.card_le_card hsub
            omega
    · have hroundQ :
          Finmap.lookupD q s'.round = Finmap.lookupD q s.round := by
        simp [hround, lookupD_insert_of_ne hqp]
      have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
        simpa [hMax] using hr
      rcases (past_start_round_condition_iff s).mp hold q hq r hrOld with
        hfuture | hzero | hquorum
      · exact Or.inl (by simpa [hroundQ] using hfuture)
      · exact Or.inr (Or.inl hzero)
      · exact Or.inr (Or.inr (transferQuorum hquorum))
  · let senders :=
      proposal_senders s evProposal ∪
        vote_senders s evPrevote ∪ vote_senders s evPrecommit
    have hsenderSub : senders ⊆ all_replicas s := by
      apply Finset.union_subset
      · exact Finset.union_subset
          (proposal_senders_subset s evProposal)
          (vote_senders_subset s evPrevote)
      · exact vote_senders_subset s evPrecommit
    obtain ⟨c, hc, hcSenders⟩ :=
      threshold_has_correct hmodel hsenderSub hcard
    have hcRound : rnd ≤ Finmap.lookupD c s.round := by
      by_contra hnot
      have hrFuture :
          rnd ∈ Finset.filter
            (fun x => x > Finmap.lookupD c s.round)
            (Finset.Icc 0 s.MaxRound) :=
        Finset.mem_filter.mpr ⟨hrnd, by omega⟩
      rcases Finset.mem_union.mp hcSenders with hleft | hpc
      · rcases Finset.mem_union.mp hleft with hprop | hpv
        · rcases Finset.mem_filter.mp hprop with
            ⟨_, m, hm, hsrc⟩
          have hne :=
            (hnofuture c hc).2 rnd hrFuture |>.1 m (hProposal hm)
          exact hne hsrc
        · rcases Finset.mem_filter.mp hpv with
            ⟨_, m, hm, hsrc⟩
          have hne :=
            (hnofuture c hc).2 rnd hrFuture |>.2.1 m (hPrevote hm)
          exact hne hsrc
      · rcases Finset.mem_filter.mp hpc with
          ⟨_, m, hm, hsrc⟩
        have hne :=
          (hnofuture c hc).2 rnd hrFuture |>.2.2 m (hPrecommit hm)
        exact hne hsrc
    intro q hq' r hr
    have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
    by_cases hqp : q = p
    · subst q
      have hroundPost : Finmap.lookupD p s'.round = rnd := by
        simp [hround]
      by_cases hfuture : r > Finmap.lookupD p s'.round
      · exact Or.inl hfuture
      · by_cases hzero : r = 0
        · exact Or.inr (Or.inl hzero)
        · right; right
          apply fromCorrect hc hcRound hr
          · simpa [hroundPost] using (show r ≤
              Finmap.lookupD p s'.round by omega)
          · exact hzero
    · have hroundQ :
          Finmap.lookupD q s'.round = Finmap.lookupD q s.round := by
        simp [hround, lookupD_insert_of_ne hqp]
      have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
        simpa [hMax] using hr
      rcases (past_start_round_condition_iff s).mp hold q hq r hrOld with
        hfuture | hzero | hquorum
      · exact Or.inl (by simpa [hroundQ] using hfuture)
      · exact Or.inr (Or.inl hzero)
      · exact Or.inr (Or.inr (transferQuorum hquorum))

def intMaxStep (acc x : Int) : Int :=
  if x > acc then x else acc

noncomputable def max_round_reached (s : State) : Int :=
  List.foldl intMaxStep 0
    (Finset.toList
      (Finset.image (fun k => Finmap.lookupD k s.round)
        (Finmap.keys s.round)))

lemma foldl_intMaxStep_ge_acc (xs : List Int) (acc : Int) :
    acc ≤ xs.foldl intMaxStep acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hstep : acc ≤ intMaxStep acc x := by
        unfold intMaxStep
        split <;> omega
      exact hstep.trans (ih (intMaxStep acc x))

lemma mem_le_foldl_intMaxStep (xs : List Int) (acc x : Int)
    (hx : x ∈ xs) :
    x ≤ xs.foldl intMaxStep acc := by
  induction xs generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with hxy | hx
      · subst x
        have hstep : y ≤ intMaxStep acc y := by
          unfold intMaxStep
          split <;> omega
        exact hstep.trans (foldl_intMaxStep_ge_acc ys _)
      · exact ih (intMaxStep acc y) hx

lemma foldl_intMaxStep_origin (xs : List Int) (acc : Int) :
    xs.foldl intMaxStep acc = acc ∨
      ∃ x ∈ xs, xs.foldl intMaxStep acc = x := by
  induction xs generalizing acc with
  | nil => exact Or.inl rfl
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rcases ih (intMaxStep acc y) with hs | ⟨x, hx, hs⟩
      · have hchoice :
            intMaxStep acc y = acc ∨ intMaxStep acc y = y := by
          unfold intMaxStep
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        rcases hchoice with hacc | hy
        · exact Or.inl (hs.trans hacc)
        · exact Or.inr ⟨y, by simp, hs.trans hy⟩
      · exact Or.inr ⟨x, by simp [hx], hs⟩

lemma round_le_max_round_reached {s : State}
    (htype : ind_type_ok s) {p : Int} (hp : p ∈ s.Corr) :
    Finmap.lookupD p s.round ≤ max_round_reached s := by
  have ht := (ind_type_ok_iff_components s).mp htype
  unfold max_round_reached
  apply mem_le_foldl_intMaxStep _ 0
  rw [Finset.mem_toList]
  apply Finset.mem_image.mpr
  refine ⟨p, ?_, rfl⟩
  rw [ht.round_keys]
  exact hp

lemma max_round_reached_nonneg (s : State) :
    0 ≤ max_round_reached s := by
  exact foldl_intMaxStep_ge_acc _ 0

lemma max_round_reached_origin {s : State}
    (htype : ind_type_ok s) :
    max_round_reached s = 0 ∨
      ∃ p ∈ s.Corr,
        max_round_reached s = Finmap.lookupD p s.round := by
  have ht := (ind_type_ok_iff_components s).mp htype
  rcases foldl_intMaxStep_origin
      (Finset.toList
        (Finset.image (fun k => Finmap.lookupD k s.round)
          (Finmap.keys s.round))) 0 with hzero | ⟨x, hx, heq⟩
  · exact Or.inl hzero
  · right
    rw [Finset.mem_toList] at hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    refine ⟨p, ?_, heq⟩
    rw [← ht.round_keys]
    exact hp

lemma rounds_below_precommit_condition_iff (s : State) :
    all_rounds_below_have_precommit_quorum s ↔
      ∀ r ∈ Finset.Icc 0 s.MaxRound,
        r < max_round_reached s →
          (pc_all s r).card ≥ 2 * s.T + 1 := by
  unfold all_rounds_below_have_precommit_quorum max_round_reached
  constructor
  · intro h r hr hlt
    have hraw := h r hr hlt
    convert hraw using 1
  · intro h r hr hlt
    have hnamed := h r hr hlt
    convert hnamed using 1
lemma next_preserves_rounds_below_precommit_quorum {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hold : all_rounds_below_have_precommit_quorum s)
    (hnext : Next s s') :
    all_rounds_below_have_precommit_quorum s' := by
  have hmono := next_messages_monotone hnext
  have htype' := next_preserves_ind_type_ok htype hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, _, _, hMax, _⟩
  have transferCard {r : Int}
      (hcard : (pc_all s r).card ≥ 2 * s.T + 1) :
      (pc_all s' r).card ≥ 2 * s'.T + 1 := by
    have hsub := pc_all_mono_frame hCorr hFaulty
      (hmono.precommits r)
    have hle := Finset.card_le_card hsub
    omega
  rw [rounds_below_precommit_condition_iff]
  intro r hr hltPost
  have hrOld : r ∈ Finset.Icc 0 s.MaxRound := by
    simpa [hMax] using hr
  by_cases hltOld : r < max_round_reached s
  · exact transferCard
      ((rounds_below_precommit_condition_iff s).mp hold r hrOld hltOld)
  · have hmaxOldLe : max_round_reached s ≤ r := by omega
    have hrNonneg : 0 ≤ r := (Finset.mem_Icc.mp hr).1
    have hmaxPostNonzero : max_round_reached s' ≠ 0 := by omega
    rcases max_round_reached_origin htype' with hzero | hsource
    · exact (hmaxPostNonzero hzero).elim
    · rcases hsource with ⟨q, hq', hmaxEq⟩
      have hq : q ∈ s.Corr := by simpa [hCorr] using hq'
      have hqPostGt :
          r < Finmap.lookupD q s'.round := by omega
      rcases next_round_evolution hnext with
          ⟨hround⟩ |
          ⟨p, hp, evidence, hevidence, hcard, hround⟩ |
          ⟨p, rnd, hp, hrnd, evProposal, evPrevote, evPrecommit,
            hProposal, hPrevote, hPrecommit, hcard, hround⟩
      · have hqLe := round_le_max_round_reached htype hq
        have hsame :
            Finmap.lookupD q s'.round =
              Finmap.lookupD q s.round := by simp [hround]
        omega
      · by_cases hqp : q = p
        · subst q
          have hpLe := round_le_max_round_reached htype hp
          have hpost :
              Finmap.lookupD p s'.round =
                Finmap.lookupD p s.round + 1 := by simp [hround]
          have hre : r = Finmap.lookupD p s.round := by omega
          have hsub :
              vote_senders s evidence ⊆ pc_all s' r := by
            intro src hsrc
            rcases Finset.mem_filter.mp hsrc with
              ⟨hall, m, hm, hsrcm⟩
            apply Finset.mem_filter.mpr
            refine
              ⟨by simpa [all_replicas, hCorr, hFaulty] using hall,
                m, ?_, hsrcm⟩
            simpa [pc_all, hre] using
              hmono.precommits (Finmap.lookupD p s.round)
                (hevidence hm)
          have hle := Finset.card_le_card hsub
          omega
        · have hsame :
              Finmap.lookupD q s'.round =
                Finmap.lookupD q s.round := by
            simp [hround, lookupD_insert_of_ne hqp]
          have hqLe := round_le_max_round_reached htype hq
          omega
      · let senders :=
          proposal_senders s evProposal ∪
            vote_senders s evPrevote ∪ vote_senders s evPrecommit
        have hsenderSub : senders ⊆ all_replicas s := by
          apply Finset.union_subset
          · exact Finset.union_subset
              (proposal_senders_subset s evProposal)
              (vote_senders_subset s evPrevote)
          · exact vote_senders_subset s evPrecommit
        obtain ⟨c, hc, hcSenders⟩ :=
          threshold_has_correct hmodel hsenderSub hcard
        have hcRound : rnd ≤ Finmap.lookupD c s.round := by
          by_contra hnot
          have hrFuture :
              rnd ∈ Finset.filter
                (fun x => x > Finmap.lookupD c s.round)
                (Finset.Icc 0 s.MaxRound) :=
            Finset.mem_filter.mpr ⟨hrnd, by omega⟩
          rcases Finset.mem_union.mp hcSenders with hleft | hpc
          · rcases Finset.mem_union.mp hleft with hprop | hpv
            · rcases Finset.mem_filter.mp hprop with
                ⟨_, m, hm, hsrc⟩
              have hne :=
                (hnofuture c hc).2 rnd hrFuture |>.1 m (hProposal hm)
              exact hne hsrc
            · rcases Finset.mem_filter.mp hpv with
                ⟨_, m, hm, hsrc⟩
              have hne :=
                (hnofuture c hc).2 rnd hrFuture |>.2.1 m (hPrevote hm)
              exact hne hsrc
          · rcases Finset.mem_filter.mp hpc with
              ⟨_, m, hm, hsrc⟩
            have hne :=
              (hnofuture c hc).2 rnd hrFuture |>.2.2 m (hPrecommit hm)
            exact hne hsrc
        have hrndLeMax :=
          hcRound.trans (round_le_max_round_reached htype hc)
        by_cases hqp : q = p
        · subst q
          have hpost : Finmap.lookupD p s'.round = rnd := by
            simp [hround]
          omega
        · have hsame :
              Finmap.lookupD q s'.round =
                Finmap.lookupD q s.round := by
            simp [hround, lookupD_insert_of_ne hqp]
          have hqLe := round_le_max_round_reached htype hq
          omega

def PrecommitLocksCondition (s : State) (p r₀ value r₁ : Int) : Prop :=
  (r₁ > r₀ ∧
      (∃ pc ∈ Finmap.lookupD r₀ s.msgs_precommit,
        (p = pc.src ∧ pc.id ≠ -1) ∧ value ≠ pc.id) ∧
        ∃ pv ∈ Finmap.lookupD r₁ s.msgs_prevote,
          p = pv.src ∧ value = pv.id) →
    ∃ r ∈ Finset.filter
        (fun x => x ≥ r₀ ∧ x < r₁) (Finset.Icc 0 s.MaxRound),
      (pv_set s r value).card ≥ 2 * s.T + 1

lemma precommit_locks_condition_iff (s : State) :
    precommit_locks_later_prevotes s ↔
      ∀ p ∈ s.Corr,
        ∀ r₀ ∈ Finset.Icc 0 s.MaxRound,
          ∀ value ∈ s.ValidValues,
            ∀ r₁ ∈ Finset.Icc 0 s.MaxRound,
              PrecommitLocksCondition s p r₀ value r₁ := by
  unfold precommit_locks_later_prevotes PrecommitLocksCondition
  constructor
  · intro h p hp r₀ hr₀ value hvalue r₁ hr₁ hante
    rcases h p hp r₀ hr₀ value hvalue r₁ hr₁ hante with
      ⟨r, hr, hcard⟩
    refine ⟨r, hr, ?_⟩
    simpa [pv_set, vote_senders, votes_for, all_replicas,
      eq_comm] using hcard
  · intro h p hp r₀ hr₀ value hvalue r₁ hr₁ hante
    rcases h p hp r₀ hr₀ value hvalue r₁ hr₁ hante with
      ⟨r, hr, hcard⟩
    refine ⟨r, hr, ?_⟩
    simpa [pv_set, vote_senders, votes_for, all_replicas,
      eq_comm] using hcard

lemma correct_precommit_gives_prevote_quorum {s : State}
    (hmodel : model_assumptions s)
    (hquorum : if_sent_precommit_then_received_two_thirds s)
    {r : Int} (hr : r ∈ Finset.Icc 0 s.MaxRound)
    {m : VoteMsg} (hm : m ∈ Finmap.lookupD r s.msgs_precommit)
    (hsrc : m.src ∈ s.Corr) (hvalue : m.id ∈ s.ValidValues) :
    (pv_set s r m.id).card ≥ 2 * s.T + 1 := by
  rcases (precommit_quorum_condition_iff s).mp hquorum
      r hr m hm hsrc with hgood | hnil
  · exact hgood.2
  · have hnotNil : m.id ≠ -1 := by
      intro heq
      rw [heq] at hvalue
      exact hmodel.2.2.2.2.2.2.2.2.1 hvalue
    exact (hnotNil hnil.1).elim

lemma next_fresh_correct_precommit_prevotes_frame {s s' : State}
    (hmodel : model_assumptions s) (hnext : Next s s')
    {r : Int} {m : VoteMsg}
    (hm : m ∈ Finmap.lookupD r s'.msgs_precommit)
    (hmOld : m ∉ Finmap.lookupD r s.msgs_precommit)
    (hsrc : m.src ∈ s.Corr) :
    s'.msgs_prevote = s.msgs_prevote := by
  have hdisjoint := hmodel.2.2.2.1
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, hp, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r₀, _, hrest⟩ := hex
    obtain ⟨_, _, _, _, _, hblock⟩ := hrest
    obtain ⟨fps, hfps, _, value, _, hprecommits⟩ := hblock
    rw [hprecommits, mem_lookupD_insert_union_iff] at hm
    rcases hm with hm | ⟨_, hm⟩
    · exact (hmOld hm).elim
    · simp only [Finset.mem_image] at hm
      rcases hm with ⟨src, hsrcFps, rfl⟩
      have hboth : src ∈ s.Corr ∩ s.Faulty :=
        Finset.mem_inter.mpr
          ⟨hsrc, Finset.mem_powerset.mp hfps hsrcFps⟩
      rw [hdisjoint] at hboth
      simp at hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      exact hprevotes
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprevotes⟩
      exact hprevotes
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprevotes, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold on_timeout_propose at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      exact hprevotes
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, hprecommits⟩
      exact (hmOld (by simpa [hprecommits] using hm)).elim

lemma latest_lock_facts_of_precommit {s : State}
    (htype : ind_type_ok s)
    (hlatest : all_latest_precommit_has_locked_round s)
    {p r : Int} (hp : p ∈ s.Corr)
    (hr : r ∈ Finset.Icc 0 s.MaxRound)
    {pc : VoteMsg} (hpc : pc ∈ Finmap.lookupD r s.msgs_precommit)
    (hsrc : p = pc.src) (hnil : pc.id ≠ -1) :
    Finmap.lookupD p s.locked_round ∈ Finset.Icc 0 s.MaxRound ∧
      r ≤ Finmap.lookupD p s.locked_round ∧
        ∃ lp ∈
            Finmap.lookupD (Finmap.lookupD p s.locked_round)
              s.msgs_precommit,
          p = lp.src ∧ lp.id = Finmap.lookupD p s.locked_value := by
  have ht := (ind_type_ok_iff_components s).mp htype
  rcases hlatest p hp with hlockNil | hlock
  · rcases hlockNil.2.2 r hr pc hpc with hne | hid
    · exact (hne hsrc).elim
    · exact (hnil hid).elim
  · have hlrType := ht.locked_rounds p hp
    simp only [Finset.mem_union, Finset.mem_insert,
      Finset.notMem_empty, or_false] at hlrType
    have hlrDom : Finmap.lookupD p s.locked_round ∈
        Finset.Icc 0 s.MaxRound := by
      rcases hlrType with hrange | heq
      · exact hrange
      · exact (hlock.1 heq).elim
    have hrKey : r ∈ Finmap.keys s.msgs_precommit := by
      rw [ht.precommit_keys]
      exact hr
    have hpcRound := ht.precommits_round r hrKey pc hpc
    have hle : r ≤ Finmap.lookupD p s.locked_round := by
      rcases hlock.2.2.1 r hr pc hpc with hbound | hid
      · rcases hbound with hne | hle
        · exact (hne hsrc).elim
        · omega
      · exact (hnil hid).elim
    exact ⟨hlrDom, hle, hlock.2.2.2⟩

lemma fresh_correct_value_prevote_gives_quorum {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hbounded : all_valid_and_locked_round_bounded s)
    (hlatest : all_latest_precommit_has_locked_round s)
    (hpcQuorum : if_sent_precommit_then_received_two_thirds s)
    (hnext : Next s s')
    {p r₀ value r₁ : Int}
    (hp : p ∈ s.Corr)
    (hr₀ : r₀ ∈ Finset.Icc 0 s.MaxRound)
    (hvalue : value ∈ s.ValidValues)
    (hr₁ : r₁ ∈ Finset.Icc 0 s.MaxRound)
    (hlt : r₀ < r₁)
    {pc pv : VoteMsg}
    (hpc : pc ∈ Finmap.lookupD r₀ s.msgs_precommit)
    (hpcsrc : p = pc.src) (hpcnil : pc.id ≠ -1)
    (hpv : pv ∈ Finmap.lookupD r₁ s'.msgs_prevote)
    (hpvOld : pv ∉ Finmap.lookupD r₁ s.msgs_prevote)
    (hpvsrc : p = pv.src) (hpvid : value = pv.id) :
    ∃ r ∈ Finset.filter
        (fun x => x ≥ r₀ ∧ x < r₁) (Finset.Icc 0 s'.MaxRound),
      (pv_set s' r value).card ≥ 2 * s'.T + 1 := by
  have hmono := next_messages_monotone hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, _, _, hMax, _⟩
  have hframeQuorum {r : Int}
      (hr : r ∈ Finset.Icc 0 s.MaxRound)
      (hrLower : r₀ ≤ r) (hrUpper : r < r₁)
      (hq : (pv_set s r value).card ≥ 2 * s.T + 1) :
      ∃ rr ∈ Finset.filter
          (fun x => x ≥ r₀ ∧ x < r₁) (Finset.Icc 0 s'.MaxRound),
        (pv_set s' rr value).card ≥ 2 * s'.T + 1 := by
    refine ⟨r, Finset.mem_filter.mpr
      ⟨by simpa [hMax] using hr, ⟨hrLower, hrUpper⟩⟩, ?_⟩
    have hsub := pv_set_mono_frame hCorr hFaulty
      (hmono.prevotes r) (v := value)
    have hle := Finset.card_le_card hsub
    omega
  rcases latest_lock_facts_of_precommit htype hlatest hp hr₀ hpc
      hpcsrc hpcnil with
    ⟨hlrRange, hr₀le, lp, hlp, hlpsrc, hlpid⟩
  have lockedQuorum
      (hlockedValue : Finmap.lookupD p s.locked_value = value)
      (hlrlt : Finmap.lookupD p s.locked_round < r₁) :
      ∃ rr ∈ Finset.filter
          (fun x => x ≥ r₀ ∧ x < r₁) (Finset.Icc 0 s'.MaxRound),
        (pv_set s' rr value).card ≥ 2 * s'.T + 1 := by
    have hlpCorr : lp.src ∈ s.Corr := by
      simpa [← hlpsrc] using hp
    have hlpValue : lp.id ∈ s.ValidValues := by
      simpa [hlpid, hlockedValue] using hvalue
    have hq := correct_precommit_gives_prevote_quorum
      hmodel hpcQuorum hlrRange hlp hlpCorr hlpValue
    have hqValue :
        (pv_set s (Finmap.lookupD p s.locked_round) value).card ≥
          2 * s.T + 1 := by
      simpa [hlpid, hlockedValue] using hq
    exact hframeQuorum hlrRange hr₀le hlrlt hqValue
  have lockLtAtPropose
      (hstep : Finmap.lookupD p s.step = Step.PROPOSE)
      (hrEq : r₁ = Finmap.lookupD p s.round) :
      Finmap.lookupD p s.locked_round < r₁ := by
    have hlrLeRound := (hbounded p hp).2
    by_contra hnot
    have heq : Finmap.lookupD p s.locked_round =
        Finmap.lookupD p s.round := by omega
    rcases (hnofuture p hp).1.2.2 with hpcStep | hdecStep | hnone
    · simp [hstep] at hpcStep
    · simp [hstep] at hdecStep
    · exact (hnone lp (by simpa [heq] using hlp)
        (by simpa [hlpsrc])).elim
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, q, hqCorr, hcorrect⟩
  · unfold faulty_step at hfaulty
    obtain ⟨_, hex, _⟩ := hfaulty
    obtain ⟨r, _, hrest⟩ := hex
    obtain ⟨_, _, _, hblock, _⟩ := hrest
    obtain ⟨fps, hfps, _, v, _, hprevotes⟩ := hblock
    rw [hprevotes, mem_lookupD_insert_union_iff] at hpv
    rcases hpv with hpv | ⟨_, hpv⟩
    · exact (hpvOld hpv).elim
    · simp only [Finset.mem_image] at hpv
      rcases hpv with ⟨src, hsrcFps, rfl⟩
      have hboth : p ∈ s.Corr ∩ s.Faulty := by
        refine Finset.mem_inter.mpr ⟨hp, ?_⟩
        simpa [hpvsrc] using Finset.mem_powerset.mp hfps hsrcFps
      rw [hmodel.2.2.2.1] at hboth
      simp at hboth
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _⟩
      rcases hact with
        ⟨hstep, _, actionValue, _, _, hprevotes, _, _⟩
      rw [hprevotes, mem_lookupD_insert_union_iff] at hpv
      rcases hpv with hpv | ⟨hrEq, hpv⟩
      · exact (hpvOld hpv).elim
      · simp at hpv
        subst pv
        have hpq : p = q := by simpa using hpvsrc
        subst q
        let condition :=
          actionValue ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round = -1 ∨
              Finmap.lookupD p s.locked_value = actionValue)
        have hvalueEq :
            value = if condition then actionValue else -1 := by
          simpa [condition] using hpvid
        have hc : condition := by
          by_contra hnot
          simp [hnot] at hvalueEq
          exact hmodel.2.2.2.2.2.2.2.2.1 (hvalueEq ▸ hvalue)
        have hactionValue : actionValue = value := by
          simpa [hc] using hvalueEq.symm
        subst actionValue
        have hlrNonNil : Finmap.lookupD p s.locked_round ≠ -1 := by
          intro heq
          rw [heq] at hlrRange
          simp at hlrRange
        have hlockedValue :
            Finmap.lookupD p s.locked_value = value :=
          hc.2.resolve_left hlrNonNil
        exact lockedQuorum hlockedValue
          (lockLtAtPropose hstep hrEq)
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _⟩
      rcases hact with
        ⟨hstep, _, actionValue, _, _, vr, hvr, _, hvrlt, _,
          hcard, hprevotes, _, _⟩
      rw [hprevotes, mem_lookupD_insert_union_iff] at hpv
      rcases hpv with hpv | ⟨hrEq, hpv⟩
      · exact (hpvOld hpv).elim
      · simp at hpv
        subst pv
        have hpq : p = q := by simpa using hpvsrc
        subst q
        let condition :=
          actionValue ∈ s.ValidValues ∧
            (Finmap.lookupD p s.locked_round ≤ vr ∨
              Finmap.lookupD p s.locked_value = actionValue)
        have hvalueEq :
            value = if condition then actionValue else -1 := by
          simpa [condition] using hpvid
        have hc : condition := by
          by_contra hnot
          simp [hnot] at hvalueEq
          exact hmodel.2.2.2.2.2.2.2.2.1 (hvalueEq ▸ hvalue)
        have hactionValue : actionValue = value := by
          simpa [hc] using hvalueEq.symm
        subst actionValue
        rcases hc.2 with hlrLeVr | hlockedValue
        · have hqOld : (pv_set s vr value).card ≥
              2 * s.T + 1 := by
            rw [← prevote_value_messages_card_eq_pv_set htype hvr]
            exact hcard
          exact hframeQuorum hvr (hr₀le.trans hlrLeVr)
            (by simpa [hrEq] using hvrlt) hqOld
        · exact lockedQuorum hlockedValue
            (lockLtAtPropose hstep hrEq)
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprevotes⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, hprevotes, _⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold on_timeout_propose at h
      rcases h with ⟨hact, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _⟩
      rcases hact with ⟨_, _, hprevotes, _, _⟩
      rw [hprevotes, mem_lookupD_insert_union_iff] at hpv
      rcases hpv with hpv | ⟨_, hpv⟩
      · exact (hpvOld hpv).elim
      · simp at hpv
        subst pv
        have : value = -1 := by simpa using hpvid
        exact (hmodel.2.2.2.2.2.2.2.2.1 (this ▸ hvalue)).elim
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hprevotes, _⟩
      exact (hpvOld (by simpa [hprevotes] using hpv)).elim

lemma next_preserves_precommit_locks_later_prevotes {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hbounded : all_valid_and_locked_round_bounded s)
    (hlatest : all_latest_precommit_has_locked_round s)
    (hpcQuorum : if_sent_precommit_then_received_two_thirds s)
    (hold : precommit_locks_later_prevotes s)
    (hnext : Next s s') :
    precommit_locks_later_prevotes s' := by
  have hmono := next_messages_monotone hnext
  have hev := next_source_evolution hnext
  rcases next_same_parameters hnext with
    ⟨hCorr, hFaulty, _, hT, hValid, _, hMax, _⟩
  rw [precommit_locks_condition_iff]
  intro p hpPost r₀ hr₀Post value hvaluePost r₁ hr₁Post hante
  have hp : p ∈ s.Corr := by simpa [hCorr] using hpPost
  have hr₀ : r₀ ∈ Finset.Icc 0 s.MaxRound := by
    simpa [hMax] using hr₀Post
  have hr₁ : r₁ ∈ Finset.Icc 0 s.MaxRound := by
    simpa [hMax] using hr₁Post
  have hvalue : value ∈ s.ValidValues := by
    simpa [hValid] using hvaluePost
  rcases hante with
    ⟨hlt, ⟨pc, hpcPost, ⟨hpcsrc, hpcnil⟩, hpcValue⟩,
      pv, hpvPost, hpvsrc, hpvValue⟩
  by_cases hpcOld : pc ∈ Finmap.lookupD r₀ s.msgs_precommit
  · by_cases hpvOld : pv ∈ Finmap.lookupD r₁ s.msgs_prevote
    · rcases (precommit_locks_condition_iff s).mp hold
          p hp r₀ hr₀ value hvalue r₁ hr₁
          ⟨hlt, ⟨pc, hpcOld, ⟨hpcsrc, hpcnil⟩, hpcValue⟩,
            pv, hpvOld, hpvsrc, hpvValue⟩ with
        ⟨r, hr, hcard⟩
      refine ⟨r, ?_, ?_⟩
      · simpa [hMax] using hr
      · have hsub := pv_set_mono_frame hCorr hFaulty
          (hmono.prevotes r) (v := value)
        have hle := Finset.card_le_card hsub
        omega
    · exact fresh_correct_value_prevote_gives_quorum
        hmodel htype hnofuture hbounded hlatest hpcQuorum hnext
        hp hr₀ hvalue hr₁ hlt hpcOld hpcsrc hpcnil
        hpvPost hpvOld hpvsrc hpvValue
  · have hprevotesFrame :=
      next_fresh_correct_precommit_prevotes_frame
        hmodel hnext hpcPost hpcOld (by simpa [← hpcsrc] using hp)
    have hpvOld : pv ∈ Finmap.lookupD r₁ s.msgs_prevote := by
      simpa [hprevotesFrame] using hpvPost
    rcases hev.precommits r₀ pc hpcPost with
        hpcWasOld | hpcFaulty | hpcFresh
    · exact (hpcOld hpcWasOld).elim
    · have hboth : p ∈ s.Corr ∩ s.Faulty := by
        exact Finset.mem_inter.mpr
          ⟨hp, by simpa [hpcsrc] using hpcFaulty⟩
      rw [hmodel.2.2.2.1] at hboth
      simp at hboth
    · have hr₀Eq : r₀ = Finmap.lookupD p s.round := by
        simpa [hpcsrc] using hpcFresh.2.1
      have hrFuture :
          r₁ ∈ Finset.filter
            (fun x => x > Finmap.lookupD p s.round)
            (Finset.Icc 0 s.MaxRound) := by
        exact Finset.mem_filter.mpr ⟨hr₁, by omega⟩
      have hnone := (hnofuture p hp).2 r₁ hrFuture |>.2.1
      exact (hnone pv hpvOld hpvsrc).elim

def PrecommitsLockValueCondition (s : State) (r value : Int) : Prop :=
  (pc_set s r value).card < 2 * s.T + 1 ∨
    ∀ later ∈ Finset.filter (fun x => x > r)
        (Finset.Icc 0 s.MaxRound),
      ∀ other ∈ s.ValidValues \ insert value ∅,
        (pv_set s later other).card < 2 * s.T + 1

lemma precommits_lock_value_condition_iff (s : State) :
    precommits_lock_value s ↔
      ∀ r ∈ Finset.Icc 0 s.MaxRound,
        ∀ value ∈ s.ValidValues,
          PrecommitsLockValueCondition s r value := by
  unfold precommits_lock_value PrecommitsLockValueCondition
  constructor <;> intro h r hr value hvalue
  · simpa [pc_set, pv_set, vote_senders, votes_for, all_replicas,
      eq_comm] using h r hr value hvalue
  · simpa [pc_set, pv_set, vote_senders, votes_for, all_replicas,
      eq_comm] using h r hr value hvalue

lemma next_preserves_precommits_lock_value {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hnofuture : all_no_future_messages_sent s)
    (hbounded : all_valid_and_locked_round_bounded s)
    (hlatest : all_latest_precommit_has_locked_round s)
    (hpcQuorum : if_sent_precommit_then_received_two_thirds s)
    (hnoeq : all_no_equivocation_by_correct s)
    (hlater : precommit_locks_later_prevotes s)
    (_hold : precommits_lock_value s)
    (hnext : Next s s') :
    precommits_lock_value s' := by
  have hmodel' := next_preserves_model_assumptions hmodel hnext
  have htype' := next_preserves_ind_type_ok htype hnext
  have hpcQuorum' :=
    next_preserves_precommit_quorum hmodel htype hpcQuorum hnext
  have hnoeq' :=
    next_preserves_no_equivocation hmodel htype hnofuture hnoeq hnext
  have hlater' :=
    next_preserves_precommit_locks_later_prevotes
      hmodel htype hnofuture hbounded hlatest hpcQuorum hlater hnext
  have sameRoundConflict {r value other : Int}
      (hr : r ∈ Finset.Icc 0 s'.MaxRound)
      (hvalue : value ∈ s'.ValidValues)
      (hother : other ∈ s'.ValidValues)
      (hne : value ≠ other)
      (hpc : (pc_set s' r value).card ≥ 2 * s'.T + 1)
      (hpv : (pv_set s' r other).card ≥ 2 * s'.T + 1) :
      False := by
    obtain ⟨c, hcCorr, hcPC⟩ :=
      quorum_has_correct hmodel'
        (vote_senders_subset s' _) hpc
    rcases mem_pc_set.mp hcPC with
      ⟨_, pc, hpcMem, hpcId, hpcSrc⟩
    have hsent :=
      hpcQuorum' r hr pc hpcMem (by simpa [hpcSrc] using hcCorr)
    have hpvValue :
        (pv_set s' r value).card ≥ 2 * s'.T + 1 := by
      rcases hsent with hgood | hnil
      · simpa [pv_set, vote_senders, votes_for, all_replicas,
          hpcId, eq_comm] using hgood.2
      · have hnotNil : pc.id ≠ -1 := by
          intro heq
          have hvalueEq : value = -1 := hpcId.trans heq
          exact hmodel'.2.2.2.2.2.2.2.2.1
            (hvalueEq ▸ hvalue)
        exact (hnotNil hnil.1).elim
    obtain ⟨d, hdCorr, hdValue, hdOther⟩ :=
      quorums_intersect_in_correct hmodel'
        (vote_senders_subset s' _) (vote_senders_subset s' _)
        hpvValue hpv
    rcases mem_pv_set.mp hdValue with
      ⟨_, mv, hmv, hmvId, hmvSrc⟩
    rcases mem_pv_set.mp hdOther with
      ⟨_, mo, hmo, hmoId, hmoSrc⟩
    rcases (hnoeq' r hr).2.1 d hdCorr with
      ⟨chosen, _, hvotes⟩
    have hv := hvotes mv hmv (by omega)
    have ho := hvotes mo hmo (by omega)
    omega
  rw [precommits_lock_value_condition_iff]
  intro r₀ hr₀ value hvalue
  by_cases hpcSmall :
      (pc_set s' r₀ value).card < 2 * s'.T + 1
  · exact Or.inl hpcSmall
  · right
    intro r hr other hother
    by_contra hpvNotSmall
    have hpcLarge :
        (pc_set s' r₀ value).card ≥ 2 * s'.T + 1 := by omega
    have hpvLarge :
        (pv_set s' r other).card ≥ 2 * s'.T + 1 := by omega
    have hrRange : r ∈ Finset.Icc 0 s'.MaxRound :=
      (Finset.mem_filter.mp hr).1
    have hrGt : r₀ < r := (Finset.mem_filter.mp hr).2
    have hotherValid : other ∈ s'.ValidValues :=
      (Finset.mem_sdiff.mp hother).1
    have hne : value ≠ other := by
      have hnmem := (Finset.mem_sdiff.mp hother).2
      have hotherNe : other ≠ value := by simpa using hnmem
      exact hotherNe.symm
    let bad :=
      Finset.filter
        (fun x => r₀ < x ∧
          (pv_set s' x other).card ≥ 2 * s'.T + 1)
        (Finset.Icc 0 s'.MaxRound)
    have hrBad : r ∈ bad := by
      exact Finset.mem_filter.mpr
        ⟨hrRange, ⟨hrGt, hpvLarge⟩⟩
    have hbad : bad.Nonempty := ⟨r, hrBad⟩
    let first := bad.min' hbad
    have hfirstBad : first ∈ bad := by
      exact Finset.min'_mem bad hbad
    have hfirstFacts := Finset.mem_filter.mp hfirstBad
    have hfirstRange : first ∈ Finset.Icc 0 s'.MaxRound :=
      hfirstFacts.1
    have hfirstGt : r₀ < first := hfirstFacts.2.1
    have hfirstQuorum :
        (pv_set s' first other).card ≥ 2 * s'.T + 1 :=
      hfirstFacts.2.2
    obtain ⟨c, hcCorr, hcPC, hcPV⟩ :=
      quorums_intersect_in_correct hmodel'
        (vote_senders_subset s' _) (vote_senders_subset s' _)
        hpcLarge hfirstQuorum
    rcases mem_pc_set.mp hcPC with
      ⟨_, pc, hpcMem, hpcId, hpcSrc⟩
    rcases mem_pv_set.mp hcPV with
      ⟨_, pv, hpvMem, hpvId, hpvSrc⟩
    have hpcNonNil : pc.id ≠ -1 := by
      intro heq
      have hvalueEq : value = -1 := hpcId.trans heq
      exact hmodel'.2.2.2.2.2.2.2.2.1
        (hvalueEq ▸ hvalue)
    have hotherPc : other ≠ pc.id := by omega
    rcases (precommit_locks_condition_iff s').mp hlater'
          c hcCorr r₀ hr₀ other hotherValid first hfirstRange
          ⟨hfirstGt,
            ⟨pc, hpcMem, ⟨by omega, hpcNonNil⟩, hotherPc⟩,
            pv, hpvMem, by omega, hpvId⟩ with
      ⟨earlier, heariler, hearlierQuorum⟩
    have hearlierRange :
        earlier ∈ Finset.Icc 0 s'.MaxRound :=
      (Finset.mem_filter.mp heariler).1
    have hearlierBounds := (Finset.mem_filter.mp heariler).2
    by_cases heq : earlier = r₀
    · subst earlier
      exact sameRoundConflict hr₀ hvalue hotherValid hne
        hpcLarge hearlierQuorum
    · have hearlierGt : r₀ < earlier := by omega
      have hearlierBad : earlier ∈ bad := by
        exact Finset.mem_filter.mpr
          ⟨hearlierRange, ⟨hearlierGt, hearlierQuorum⟩⟩
      have hminimum : first ≤ earlier :=
        Finset.min'_le bad earlier hearlierBad
      omega

theorem next_preserves_ind_inv {s s' : State}
    (hmodel : model_assumptions s)
    (htype : ind_type_ok s)
    (hinv : ind_inv s)
    (hnext : Next s s') :
    ind_inv s' := by
  rcases (ind_inv_iff_named s).mp hinv with
    ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
      h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈,
      h₁₉, h₂₀, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅⟩
  have h₁' :=
    next_preserves_no_future_messages hmodel htype h₁ hnext
  have h₂' := next_preserves_prevote_sent h₂ hnext
  have h₃' := next_preserves_precommit_sent h₃ hnext
  have h₄' :=
    next_preserves_decided_received_proposal h₄ h₆ hnext
  have h₅' :=
    next_preserves_decided_received_two_thirds htype h₅ h₆ hnext
  have h₆' := next_preserves_decided_valid h₆ hnext
  have h₇' :=
    next_preserves_locked_round_iff_locked_value
      hmodel htype h₇ hnext
  have h₈' :=
    next_preserves_valid_round_iff_valid_value
      hmodel htype h₈ hnext
  have h₉' :=
    next_preserves_valid_and_locked_round_bounded h₉ hnext
  have h₁₀' :=
    next_preserves_valid_round_quorum htype h₁₀ hnext
  have h₁₁' :=
    next_preserves_locked_sent_commit htype h₁₁ hnext
  have h₁₂' :=
    next_preserves_latest_precommit hmodel htype h₁ h₁₂ hnext
  have h₁₃' :=
    next_preserves_prevote_cause hmodel htype h₁₃ hnext
  have h₁₄' :=
    next_preserves_precommit_has_prevote hmodel h₁₄ h₂ hnext
  have h₁₅' :=
    next_preserves_precommit_quorum hmodel htype h₁₅ hnext
  have h₁₆' :=
    next_preserves_no_equivocation hmodel htype h₁ h₁₆ hnext
  have h₁₇' :=
    next_preserves_precommits_lock_value
      hmodel htype h₁ h₉ h₁₂ h₁₅ h₁₆ h₁₈ h₁₇ hnext
  have h₁₈' :=
    next_preserves_precommit_locks_later_prevotes
      hmodel htype h₁ h₉ h₁₂ h₁₅ h₁₈ hnext
  have h₁₉' :=
    next_preserves_locked_proposer_reproposes
      hmodel htype h₁ h₁₂ h₂₃ h₁₉ hnext
  have h₂₀' :=
    next_preserves_past_start_round hmodel h₁ h₂₀ hnext
  have h₂₁' :=
    next_preserves_rounds_below_precommit_quorum
      hmodel htype h₁ h₂₁ hnext
  have h₂₂' :=
    next_preserves_valid_current_precommitted h₂₂ h₉ hnext
  have h₂₃' :=
    next_preserves_locked_below_valid h₂₃ h₉ hnext
  have h₂₄' :=
    next_preserves_valid_precommitted h₂₄ h₃ hnext
  have h₂₅' :=
    next_preserves_correct_proposal_round
      htype h₉ h₂₂ h₂₅ hmodel hnext
  exact (ind_inv_iff_named s').mpr
    ⟨h₁', h₂', h₃', h₄', h₅', h₆', h₇', h₈', h₉', h₁₀',
      h₁₁', h₁₂', h₁₃', h₁₄', h₁₅', h₁₆', h₁₇', h₁₈',
      h₁₉', h₂₀', h₂₁', h₂₂', h₂₃', h₂₄', h₂₅'⟩

theorem typed_ind_inv_next {s s' : State}
    (hmodel : model_assumptions s)
    (hinv : typed_ind_inv s)
    (hnext : Next s s') :
    typed_ind_inv s' := by
  rcases (typed_ind_inv_iff s).mp hinv with ⟨htype, hind⟩
  exact (typed_ind_inv_iff s').mpr
    ⟨next_preserves_ind_type_ok htype hnext,
      next_preserves_ind_inv hmodel htype hind hnext⟩

end tendermint_single_indinv
