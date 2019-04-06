/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2008 Tord Romstad (Glaurung author)
  Copyright (C) 2008-2015 Marco Costalba, Joona Kiiski, Tord Romstad
  Copyright (C) 2015-2019 Marco Costalba, Joona Kiiski, Gary Linscott, Tord Romstad

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <cassert>

#include "bitboard.h"
#include "pawns.h"
#include "position.h"
#include "thread.h"

namespace {

  #define V Value
  #define S(mg, eg) make_score(mg, eg)

  // Pawn penalties
  constexpr Score Backward = S( 9, 24);
  constexpr Score Doubled  = S(11, 56);
  constexpr Score Isolated = S( 5, 15);

  // Connected pawn bonus
  constexpr int Connected[RANK_NB] = { 0, 13, 24, 18, 65, 100, 175, 330 };

  // Strength of pawn shelter for our king by [file][rank].
  // RANK_1 = 0 is used for files where we have no pawn, or pawn is behind our king.
  constexpr Value ShelterStrength[FILE_NB][RANK_NB] = {
    { V( -8), V( 84), V( 98), V( 74), V( 52), V( 17), V(  25) },
    { V(-53), V( 51), V( 28), V(-41), V(-22), V(-15), V( -64) },
    { V( -6), V( 76), V( 35), V( -2), V( 37), V( -1), V( -41) },
    { V(-46), V(-18), V(-32), V(-56), V(-41), V(-60), V(-154) },
    { V(-56), V( -5), V(-26), V(-60), V(-38), V(-62), V(-130) },
    { V(-15), V( 72), V( 24), V(-10), V( 22), V( -2), V( -65) },
    { V(-54), V( 64), V( 24), V(-44), V(-28), V(-22), V( -56) },
    { V(  6), V( 71), V( 89), V( 48), V( 22), V( 25), V(  21) }
  };

  constexpr Value ShelterStrengthKSB[FILE_NB][RANK_NB] = {
    { V(  4), V( 76), V( 89), V( 45), V( 30), V( 23), V(  13) },
    { V(-63), V( 81), V( 43), V(-80), V(-48), V(-19), V( -57) },
    { V(-12), V( 45), V( 24), V( 39), V( 46), V( 18), V( -43) },
    { V(  0), V( -5), V(-42), V(-67), V(  0), V(  0), V(   0) },
    { V(  0), V(-19), V(-46), V(-58), V(-39), V(  0), V(   0) },
    { V(  9), V( 76), V( 24), V(-14), V( 34), V( -8), V( -39) },
    { V(-53), V( 50), V( 25), V(-35), V(-37), V(-24), V( -88) },
    { V(-14), V( 91), V( 74), V( 66), V( 67), V( 16), V(  32) }
  };

  constexpr Value ShelterStrengthQSB[FILE_NB][RANK_NB] = {
    { V(  2), V(106), V( 90), V( 58), V( 43), V( 28), V(  28) },
    { V(-59), V( 43), V( 50), V(-67), V(-38), V( -6), V( -64) },
    { V( -2), V( 60), V( 13), V( -8), V( 38), V(-18), V( -40) },
    { V(  0), V( -3), V(-40), V(-60), V(-50), V(  0), V(   0) },
    { V(  0), V( 20), V(-29), V(-66), V(  0), V(  0), V(   0) },
    { V(-17), V( 60), V( 38), V(-23), V( 47), V(-12), V( -53) },
    { V(-45), V( 69), V( 29), V(-49), V( -8), V(-40), V( -81) },
    { V(  0), V( 80), V(102), V( 59), V( 33), V( 21), V(  17) }
  };

  // Danger of enemy pawns moving toward our king by [file][rank].
  // RANK_1 = 0 is used for files where the enemy has no pawn, or their pawn
  // is behind our king.
  // The rank is relative to the king targeted by the potential pawn storm.
  constexpr Value UnblockedStorm[FILE_NB][RANK_NB] = {
    { V( 85), V( 98), V(134), V(104), V(47), V( 47), V( 54) },
    { V( 49), V(-14), V(135), V( 50), V(55), V(  2), V( 26) },
    { V(  4), V( 51), V(171), V( 30), V( 5), V( -8), V(  6) },
    { V(-12), V(-11), V( 74), V( 25), V(11), V(-25), V(-22) },
    { V( -1), V(-12), V( 97), V( 17), V( 8), V(-15), V(  0) },
    { V(  5), V( 66), V(159), V( 29), V( 3), V(-10), V(  2) },
    { V( 53), V(-13), V(134), V( 45), V(27), V(-10), V( 20) },
    { V( 84), V( 84), V(114), V( 97), V(69), V( 53), V( 51) }
  };

  constexpr Value UnblockedStormKSB[FILE_NB][RANK_NB] = {
    { V( 91), V(107), V(122), V( 97), V(53), V( 17), V( 41) },
    { V( 20), V( -6), V(126), V( 62), V(48), V(  6), V( 26) },
    { V( 16), V( 60), V(155), V( 42), V( 9), V(-17), V( 10) },
    { V(  0), V(  0), V(  0), V(  0), V( 0), V(  0), V(  0) },
    { V(  0), V(  0), V(  0), V(  0), V( 0), V(  0), V(  0) },
    { V( -8), V( 53), V(172), V( 37), V( 3), V(-38), V( 21) },
    { V( 49), V( 16), V(125), V( 48), V(35), V(-21), V( 36) },
    { V(100), V(111), V( 92), V(102), V(70), V( 59), V( 44) }
  };

  constexpr Value UnblockedStormQSB[FILE_NB][RANK_NB] = {
    { V( 90), V( 99), V(124), V(68), V(41), V( 59), V( 54) },
    { V( 41), V( -7), V(128), V(31), V(28), V( -4), V( 16) },
    { V( -9), V( 50), V(157), V(46), V(21), V(-18), V( -4) },
    { V(  0), V(  0), V(  0), V( 0), V( 0), V(  0), V(  0) },
    { V(  0), V(  0), V(  0), V( 0), V( 0), V(  0), V(  0) },
    { V( -2), V( 47), V(156), V(35), V(33), V(-12), V(-10) },
    { V( 40), V( 10), V(122), V(43), V(22), V(-21), V( 23) },
    { V( 85), V(110), V(114), V(93), V(72), V( 37), V( 49) }
  };

  #undef S
  #undef V

  template<Color Us>
  Score evaluate(const Position& pos, Pawns::Entry* e) {

    constexpr Color     Them = (Us == WHITE ? BLACK : WHITE);
    constexpr Direction Up   = (Us == WHITE ? NORTH : SOUTH);
    constexpr Direction Down = (Us == WHITE ? SOUTH : NORTH);

    constexpr Bitboard d5e4 = 0x0810000000ULL;
    constexpr Bitboard d4e5 = 0x1008000000ULL;

    Bitboard b, neighbours, stoppers, doubled, support, phalanx;
    Bitboard lever, leverPush;
    Square s;
    bool opposed, backward;
    Score score = SCORE_ZERO;
    const Square* pl = pos.squares<PAWN>(Us);

    Bitboard ourPawns   = pos.pieces(  Us, PAWN);
    Bitboard theirPawns = pos.pieces(Them, PAWN);

    e->passedPawns[Us] = e->pawnAttacksSpan[Us] = e->weakUnopposed[Us] = 0;
    e->semiopenFiles[Us] = 0xFF;
    e->kingSquares[Us]   = SQ_NONE;
    e->pawnAttacks[Us]   = pawn_attacks_bb<Us>(ourPawns);
    e->pawnsOnSquares[Us][BLACK] = popcount(ourPawns & DarkSquares);
    e->pawnsOnSquares[Us][WHITE] = pos.count<PAWN>(Us) - e->pawnsOnSquares[Us][BLACK];

    if (   (ourPawns   & d4e5) == d4e5
        && (shift<Down>(theirPawns) & d4e5) == d4e5)
        e->centerStatus[Us] = (Us == WHITE) ? KS_BLOCK : QS_BLOCK;
    else if((ourPawns  & d5e4) == d5e4
        && (shift<Down>(theirPawns) & d5e4) == d5e4)
        e->centerStatus[Us] = (Us == WHITE) ? QS_BLOCK : KS_BLOCK;
    else
        e->centerStatus[Us] = NO_ADV_BLOCK;

    // Loop through all pawns of the current color and score each pawn
    while ((s = *pl++) != SQ_NONE)
    {
        assert(pos.piece_on(s) == make_piece(Us, PAWN));

        File f = file_of(s);

        e->semiopenFiles[Us]   &= ~(1 << f);
        e->pawnAttacksSpan[Us] |= pawn_attack_span(Us, s);

        // Flag the pawn
        opposed    = theirPawns & forward_file_bb(Us, s);
        stoppers   = theirPawns & passed_pawn_span(Us, s);
        lever      = theirPawns & PawnAttacks[Us][s];
        leverPush  = theirPawns & PawnAttacks[Us][s + Up];
        doubled    = ourPawns   & (s - Up);
        neighbours = ourPawns   & adjacent_files_bb(f);
        phalanx    = neighbours & rank_bb(s);
        support    = neighbours & rank_bb(s - Up);

        // A pawn is backward when it is behind all pawns of the same color
        // on the adjacent files and cannot be safely advanced.
        backward =  !(ourPawns & pawn_attack_span(Them, s + Up))
                  && (stoppers & (leverPush | (s + Up)));

        // Passed pawns will be properly scored in evaluation because we need
        // full attack info to evaluate them. Include also not passed pawns
        // which could become passed after one or two pawn pushes when are
        // not attacked more times than defended.
        if (   !(stoppers ^ lever ^ leverPush)
            && (support || !more_than_one(lever))
            && popcount(phalanx) >= popcount(leverPush))
            e->passedPawns[Us] |= s;

        else if (   stoppers == square_bb(s + Up)
                 && relative_rank(Us, s) >= RANK_5)
        {
            b = shift<Up>(support) & ~theirPawns;
            while (b)
                if (!more_than_one(theirPawns & PawnAttacks[Us][pop_lsb(&b)]))
                    e->passedPawns[Us] |= s;
        }

        // Score this pawn
        if (support | phalanx)
        {
            int r = relative_rank(Us, s);
            int v = phalanx ? Connected[r] + Connected[r + 1] : 2 * Connected[r];
            v = 17 * popcount(support) + (v >> (opposed + 1));
            score += make_score(v, v * (r - 2) / 4);
        }
        else if (!neighbours)
            score -= Isolated, e->weakUnopposed[Us] += !opposed;

        else if (backward)
            score -= Backward, e->weakUnopposed[Us] += !opposed;

        if (doubled && !support)
            score -= Doubled;
    }

    return score;
  }

} // namespace

namespace Pawns {

/// Pawns::probe() looks up the current position's pawns configuration in
/// the pawns hash table. It returns a pointer to the Entry if the position
/// is found. Otherwise a new Entry is computed and stored there, so we don't
/// have to recompute all when the same pawns configuration occurs again.

Entry* probe(const Position& pos) {

  Key key = pos.pawn_key();
  Entry* e = pos.this_thread()->pawnsTable[key];

  if (e->key == key)
      return e;

  e->key = key;
  e->scores[WHITE] = evaluate<WHITE>(pos, e);
  e->scores[BLACK] = evaluate<BLACK>(pos, e);
  e->passedCount= popcount(e->passedPawns[WHITE] | e->passedPawns[BLACK]);

  return e;
}


/// Entry::evaluate_shelter() calculates the shelter bonus and the storm
/// penalty for a king, looking at the king file and the two closest files.

template<Color Us>
Value Entry::evaluate_shelter(const Position& pos, Square ksq) {

  constexpr Color     Them = (Us == WHITE ? BLACK : WHITE);
  constexpr Direction Down = (Us == WHITE ? SOUTH : NORTH);
  constexpr Bitboard  BlockRanks = (Us == WHITE ? Rank1BB | Rank2BB : Rank8BB | Rank7BB);

  Bitboard b = pos.pieces(PAWN) & ~forward_ranks_bb(Them, ksq);
  Bitboard ourPawns = b & pos.pieces(Us);
  Bitboard theirPawns = b & pos.pieces(Them);

  Value safety = (shift<Down>(theirPawns) & (FileABB | FileHBB) & BlockRanks & ksq) ?
                 Value(374) : Value(5);

  File center = clamp(file_of(ksq), FILE_B, FILE_G);
  for (File f = File(center - 1); f <= File(center + 1); ++f)
  {
      b = ourPawns & file_bb(f);
      Rank ourRank = b ? relative_rank(Us, backmost_sq(Us, b)) : RANK_1;

      b = theirPawns & file_bb(f);
      Rank theirRank = b ? relative_rank(Us, frontmost_sq(Them, b)) : RANK_1;

      safety += (centerStatus[Us] == KS_BLOCK) ? ShelterStrengthKSB[f][ourRank] :
                (centerStatus[Us] == QS_BLOCK) ? ShelterStrengthQSB[f][ourRank] :
                                                 ShelterStrength[f][ourRank];

      // Apply unblocked storm if our backmost pawn in a file is not immediately blocked
      // by the frontmost enemy pawn in the file.
      safety -= (ourRank && (ourRank == theirRank - 1)) ? 66 * (theirRank == RANK_3)
                                                        : (centerStatus[Them] == KS_BLOCK)
                                                        ? UnblockedStormKSB[f][theirRank]
                                                        : (centerStatus[Them] == QS_BLOCK)
                                                        ? UnblockedStormQSB[f][theirRank]
                                                        : UnblockedStorm[f][theirRank];
  }

  return safety;
}


/// Entry::do_king_safety() calculates a bonus for king safety. It is called only
/// when king square changes, which is about 20% of total king_safety() calls.

template<Color Us>
Score Entry::do_king_safety(const Position& pos) {

  Square ksq = pos.square<KING>(Us);
  kingSquares[Us] = ksq;
  castlingRights[Us] = pos.castling_rights(Us);
  int minKingPawnDistance = 0;

  Bitboard pawns = pos.pieces(Us, PAWN);
  if (pawns)
      while (!(DistanceRingBB[ksq][++minKingPawnDistance] & pawns)) {}

  Value bonus = evaluate_shelter<Us>(pos, ksq);

  // If we can castle use the bonus after the castling if it is bigger
  if (pos.can_castle(Us | KING_SIDE))
      bonus = std::max(bonus, evaluate_shelter<Us>(pos, relative_square(Us, SQ_G1)));

  if (pos.can_castle(Us | QUEEN_SIDE))
      bonus = std::max(bonus, evaluate_shelter<Us>(pos, relative_square(Us, SQ_C1)));

  return make_score(bonus, -16 * minKingPawnDistance);
}

// Explicit template instantiation
template Score Entry::do_king_safety<WHITE>(const Position& pos);
template Score Entry::do_king_safety<BLACK>(const Position& pos);

} // namespace Pawns
