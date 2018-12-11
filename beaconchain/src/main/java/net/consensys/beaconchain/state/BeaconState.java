/*
 * Copyright 2018 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */

package net.consensys.beaconchain.state;

import static com.google.common.base.Preconditions.checkArgument;
import static net.consensys.beaconchain.Constants.*;

import net.consensys.beaconchain.datastructures.BeaconChainState.CandidatePoWReceiptRootRecord;
import net.consensys.beaconchain.datastructures.BeaconChainState.CrosslinkRecord;
import net.consensys.beaconchain.datastructures.BeaconChainState.ForkData;
import net.consensys.beaconchain.datastructures.BeaconChainState.PendingAttestationRecord;
import net.consensys.beaconchain.datastructures.BeaconChainState.ShardCommittee;
import net.consensys.beaconchain.datastructures.BeaconChainState.ShardReassignmentRecord;
import net.consensys.beaconchain.datastructures.BeaconChainState.ValidatorRecord;
import net.consensys.beaconchain.ethereum.core.Hash;
import net.consensys.beaconchain.util.bytes.Bytes3;
import net.consensys.beaconchain.util.bytes.Bytes32;
import net.consensys.beaconchain.util.uint.UInt64;

import java.util.Arrays;

import com.google.common.annotations.VisibleForTesting;


public class BeaconState {

  // Validator registry
  private ValidatorRecord[] validator_registry;
  private UInt64 validator_registry_latest_change_slot;
  private UInt64 validator_registry_exit_count;
  private Hash validator_registry_delta_chain_tip;

  // Randomness and committees
  private Hash randao_mix;
  private Hash next_seed;
  private ShardCommittee[][] shard_committees_at_slots;
  private int[][] persistent_committees;
  private ShardReassignmentRecord[] persistent_committee_reassignments;

  // Finality
  private UInt64 previous_justified_slot;
  private UInt64 justified_slot;
  private UInt64 justified_slot_bitfield;
  private UInt64 finalized_slot;

  // Recent state
  private CrosslinkRecord[] latest_crosslinks;
  private UInt64 latest_state_recalculation_slot;
  private Hash[] latest_block_hashes;
  private UInt64[] latest_penalized_exit_balances;
  private PendingAttestationRecord[] latest_attestations;

  // PoW receipt root
  private Hash processed_pow_receipt_root;
  private CandidatePoWReceiptRootRecord[] candidate_pow_receipt_roots;

  // Misc
  private UInt64 genesis_time;
  private ForkData fork_data;


  /**
   * Checks if ``validator`` is active
   * @param validator
   * @return
   */
  private boolean is_active_validator(ValidatorRecord validator) {
    return validator.status == UInt64.valueOf(ACTIVE) || validator.status == UInt64.valueOf(ACTIVE_PENDING_EXIT);
  }


  /**
   * Gets indices of active validators from ``validators``.
   * @param validators
   * @return
   */
  private int[] get_active_validator_indices(ValidatorRecord[] validators) {
    int index = 0;
    int[] active_validators = new int[];
    for (int i = 0; i < validators.length; i++) {
      if (is_active_validator(validators[i])) {
        active_validators[index] = i;
        index++;
      }
    }
    return active_validators;
  }


  /**
   * Shuffles ``validators`` into shard committees using ``seed`` as entropy.
   * @param seed
   * @param validators
   * @param crosslinking_start_shard
   * @return
   */
  private ShardAndCommittee[][] get_new_shuffling(Hash seed, ValidatorRecord[] validators, int crosslinking_start_shard) {
    int[] active_validator_indices = get_active_validator_indices(validators);
    int committees_per_slot = BeaconStateHelperFunctions.clamp(1, SHARD_COUNT / EPOCH_LENGTH,
        active_validator_indices.length / EPOCH_LENGTH / TARGET_COMMITTEE_SIZE);

    // Shuffle with seed
    Object[] shuffled_active_validator_indices =
        BeaconStateHelperFunctions.shuffle((active_validator_indices, seed);

    // Split the shuffled list into epoch_length pieces
    Object[] validators_per_slot =
        BeaconStateHelperFunctions.split(shuffled_active_validator_indices, EPOCH_LENGTH);

    ShardAndCommittee[][] output;

    for (int slot = 0; slot < validators_per_slot.length; slot++) {
      // Split the shuffled list into committees_per_slot pieces
      Object[] shard_indices =
          BeaconStateHelperFunctions.split(validators_per_slot[slot], committees_per_slot);

      int shard_id_start = crosslinking_start_shard + slot * committees_per_slot;

      for (int shard_position = 0; shard_position < shard_indices.length; shard_position++) {
        shard_indices[shard_position] =
            new ShardAndCommittee(((shard_id_start + shard_position) % SHARD_COUNT,
                shard_indices[shard_position], active_validator_indices.length);
      }

      output[slot] = shards_and_committees_for_slot;
    }

    return output;
  }


  /**
   * Returns the ``ShardCommittee`` for the ``slot``.
   * @param state
   * @param slot
   * @return
   */
  private ShardAndCommittee[] get_shard_committees_at_slot(BeaconState state, int slot) {
    int earliest_slot_in_array = (int) state.latest_state_recalculation_slot.getValue() - EPOCH_LENGTH;
    assert earliest_slot_in_array <= slot && slot < earliest_slot_in_array + EPOCH_LENGTH * 2;
    return state.shard_committees_at_slots[slot - earliest_slot_in_array];
  }


  /**
   * Returns the block hash at a recent ``slot``.
   * @param state
   * @param current_block
   * @param slot
   * @return
   */
  private Hash get_block_hash(BeaconState state, BeaconBlock current_block, int slot) {
    UInt64 earliest_slot_in_array = current_block.slot.minus(UInt64.valueOf(state.latest_block_hashes.length));
    assert earliest_slot_in_array.getValue() <= slot && slot < current_block.slot.getValue();
    return state.latest_block_hashes[slot - (int) earliest_slot_in_array.getValue()];
  }


  /**
   * Returns the beacon proposer index for the ``slot``.
   * @param state
   * @param slot
   * @return
   */
  private int get_beacon_proposer_index(BeaconState state, int slot) {
    int[] first_committee = get_shard_committees_at_slot(state, slot)[0].committee;
    return first_committee[slot % first_committee.length];
  }


  /**
   *
   * @param latest_block
   * @param latest_hash
   * @return
   */
  private Hash[] get_updated_ancestor_hashes(BeaconBlock latest_block, Hash latest_hash) {
    Hash[] new_ancestor_hashes = latest_block.ancestor_hashes.clone();
    for (int i = 0; i < 32; i++) {
      if (latest_block.slot.getValue() % Math.pow(2, i) == 0) {
        new_ancestor_hashes[i] = latest_hash;
      }
    }
    return new_ancestor_hashes;
  }


  /**
   *   Returns the participant indices at for the ``attestation_data`` and ``participation_bitfield``.
   * @param state
   * @param attestation_data
   * @param participation_bitfield
   * @return
   */
  private int[] get_attestation_participants(BeaconState state, AttestationData attestation_data,
                                             Bytes32 participation_bitfield) {

    // Find the relevant committee
    ShardAndCommittee[] shard_committees = get_shard_committees_at_slot(state, (int) attestation_data.slot.getValue());
    ShardAndCommittee[] shard_committee = new ShardAndCommittee[];
    int index = 0;
    for (int i = 0; i < shard_committees.length; i++) {
      if (shard_committees[i].shard == attestation_data.shard) {
        shard_committee[index] = shard_committees[i];
        index++;
      }
    }
    assert participation_bitfield.size() == ceil_div8(shard_committee.committee.length);

    // Find the participating attesters in the committee
    int[] participants = new int[];
    index = 0;
    for (int i = 0; i < shard_committee.committee.length; i++) {
      int participation_bit = (participation_bitfield[i/8] >> (7 - (i % 8))) % 2;
      if (participation_bit == 1) {
        participants[index] = shard_committee.committee[i];
      }
    }
  }


  /**
   * Returns the effective balance (also known as "balance at stake") for the ``validator``.
   * @param validator
   * @return
   */
  private int get_effective_balance(ValidatorRecord validator) {
    return Math.min((int) validator.balance.getValue(), MAX_DEPOSIT);
  }


  /**
   * Compute the next hash in the validator registry delta hash chain.
   * @param current_validator_registry_delta_chain_tip
   * @param index
   * @param pubkey
   * @param flag
   * @return
   */
  private Hash get_new_validator_registry_delta_chain_tip(Hash current_validator_registry_delta_chain_tip,
                                                          int index, int pubkey, int flag) {
    return Hash.hash(current_validator_registry_delta_chain_tip +
            Bytes1(flag) +
            Bytes3(index) +
            Bytes32(pubkey))
  }


  /**
   *
   * @param fork_data
   * @param slot
   * @param domain_type
   * @return
   */
  private int get_domain(ForkData fork_data, int slot, int domain_type) {
    return get_fork_version(fork_data, slot) * (int) Math.pow(2, 32) + domain_type;
  }


  /**
   *
   * @param state
   * @param votes
   * @return
   */
  private boolean verify_casper_votes(BeaconState state, SlashableVoteData votes) {
    if ((votes.aggregate_signature_poc_0_indices.length + votes.aggregate_signature_poc_1_indices.length)
        > MAX_CASPER_VOTES) {
      return false;
    }
//  pubs = [aggregate_pubkey([state.validators[i].pubkey for i in votes.aggregate_signature_poc_0_indices]),
//  aggregate_pubkey([state.validators[i].pubkey for i in votes.aggregate_signature_poc_1_indices])]

//      return BLSMultiVerify(pubkeys=pubs, msgs=[SSZTreeHash(votes)+bytes1(0), SSZTreeHash(votes)+bytes1(1), sig=aggregate_signature)
  }


  /**
   * The largest integer ``x`` such that ``x**2`` is less than ``n``.
   * @param n
   * @return
   */
  private int integer_squareroot(int n) {
    int x = n;
    int y = x + 1 / 2;
    while (y < x) {
      x = y;
      y = x + n / x / 2;
    }
    return x;
  }


  /**
   *
   * @param validators
   * @param current_slot
   * @return
   */
  private int min_empty_validator_index(ValidatorRecord[] validators, int current_slot) {
    for (int i = 0; i < validators.length; i++) {
      ValidatorRecord v = validators[i];
      if (v.balance == UInt64.valueOf(0) && v.latest_status_change_slot.getValue() + ZERO_BALANCE_VALIDATOR_TTL
          <= current_slot) {
        return i;
      }
    }
    return -1;
  }

  private int get_fork_version(ForkData fork_data, int slot) {
    if (slot < fork_data.fork_slot.getValue()) {
      return (int) fork_data.pre_fork_version.getValue();
    }
    return (int) fork_data.post_fork_version.getValue();
  }









  static class BeaconStateHelperFunctions {


    /**
     * Converts int to Bytes3.
     *
     * @param seed  converted
     * @return      converted Bytes3
     * @throws IllegalArgumentException if seed is a negative value.
     */
    @VisibleForTesting
    static Bytes3 intToBytes3(int seed) {
      checkArgument(seed > 0, "Expected positive seed but got %s", seed);
      byte[] bytes = new byte[3];
      bytes[0] = (byte) (seed >> 16);
      bytes[1] = (byte) (seed >> 8);
      bytes[2] = (byte) seed;
      return Bytes3.wrap(bytes);
    }

    /**
     * Converts byte[] to int.
     *
     * @param src   byte[]
     * @param pos   Index in Byte[] array
     * @return      converted int
     * @throws IllegalArgumentException if pos is a negative value.
     */
    @VisibleForTesting
    static int bytes3ToInt(Hash src, int pos) {
      checkArgument(pos >= 0, "Expected positive pos but got %s", pos);
      return ((src.extractArray()[pos] & 0xF) << 16) |
          ((src.extractArray()[pos + 1] & 0xFF) << 8) |
          (src.extractArray()[pos + 2] & 0xFF);
    }


    /**
     * Returns the shuffled ``values`` with seed as entropy.
     *
     * @param values    The array.
     * @param seed      Initial seed value used for randomization.
     * @return          The shuffled array.
     */
    @VisibleForTesting
    static Object[] shuffle(Object[] values, Hash seed) {

      int values_count = values.length;

      // Entropy is consumed from the seed in 3-byte (24 bit) chunks.
      int rand_bytes = 3;
      // The highest possible result of the RNG.
      int rand_max = (int) Math.pow(2, (rand_bytes * 8) - 1);

      // The range of the RNG places an upper-bound on the size of the list that
      // may be shuffled. It is a logic error to supply an oversized list.
      assert values_count < rand_max;

      Object[] output = values.clone();
      Hash source = seed;
      int index = 0;

      while (index < values_count - 1) {
        // Re-hash the `source` to obtain a new pattern of bytes.
        source = Hash.hash(source);

        // List to hold values for swap below.
        Object tmp;

        // Iterate through the `source` bytes in 3-byte chunks
        for (int position = 0; position < (32 - (32 % rand_bytes)); position += rand_bytes) {
          // Determine the number of indices remaining in `values` and exit
          // once the last index is reached.
          int remaining = values_count - index;
          if (remaining == 1) break;

          // Read 3-bytes of `source` as a 24-bit big-endian integer.
          int sample_from_source = bytes3ToInt(source, position);


          // Sample values greater than or equal to `sample_max` will cause
          // modulo bias when mapped into the `remaining` range.
          int sample_max = rand_max - rand_max % remaining;

          // Perform a swap if the consumed entropy will not cause modulo bias.
          if (sample_from_source < sample_max) {
            // Select a replacement index for the current index
            int replacement_position = (sample_from_source % remaining) + index;
            // Swap the current index with the replacement index.
            tmp = output[index];
            output[index] = output[replacement_position];
            output[replacement_position] = tmp;
            index += 1;
          }

        }

      }

      return output;
    }


    /**
     * Splits ``values`` into ``split_count`` pieces.
     *
     * @param values          The original list of validators.
     * @param split_count     The number of pieces to split the array into.
     * @return                The list of validators split into N pieces.
     */
    static Object[] split(Object[] values, int split_count) {
      checkArgument(split_count > 0, "Expected positive split_count but got %s", split_count);

      int list_length = values.length;

      Object[] split_arr = new Object[split_count];

      for (int i = 0; i < split_count; i++) {
        int startIndex = list_length * i / split_count;
        int endIndex = list_length * (i + 1) / split_count;
        Object[] new_split = Arrays.copyOfRange(values, startIndex, endIndex);
        split_arr[i] = new_split;
      }

      return split_arr;

    }

    /**
     * A helper method for readability.
     */
    static int clamp(int minval, int maxval, int x) {
      if (x <= minval) return minval;
      if (x >= maxval) return maxval;
      return x;
    }



  }

}
