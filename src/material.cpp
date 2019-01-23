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

#include <algorithm> // For std::min
#include <cassert>
#include <cstring>   // For std::memset

#include "material.h"
#include "thread.h"

using namespace std;

namespace {

  // Polynomial material imbalance parameters

  constexpr int QuadraticOurs[][PIECE_TYPE_NB] = {
    //            OUR PIECES
    // pair pawn knight bishop rook queen
    {1438                               }, // Bishop pair
    {  40,   38                         }, // Pawn
    {  32,  255, -62                    }, // Knight      OUR PIECES
    {   0,  104,   4,    0              }, // Bishop
    { -26,   -2,  47,   105,  -208      }, // Rook
    {-189,   24, 117,   133,  -134, -6  }  // Queen
  };

  constexpr int QuadraticTheirs[][PIECE_TYPE_NB] = {
    //           THEIR PIECES
    // pair pawn knight bishop rook queen
    {   0                               }, // Bishop pair
    {  36,    0                         }, // Pawn
    {   9,   63,   0                    }, // Knight      OUR PIECES
    {  59,   65,  42,     0             }, // Bishop
    {  46,   39,  24,   -24,    0       }, // Rook
    {  97,  100, -42,   137,  268,    0 }  // Queen
  };

  int A1 = 277;
  int A2 =-313;
  int A3 =   7;
  int A4 =-157;
  int A5 =  87;
  int A6 =  85;
  int B1 = -16;
  int B2 =-313;
  int B3 =-160;
  int B4 = -56;
  int B5 = 192;
  int B6 = -89;
  int C1 = 268;
  int C2 = -99;
  int C3 =  98;
  int C4 = 268;
  int C5 = -99;
  int C6 =  98;
  int D1 = -40;
  int D2 = 390;
  int D3 =  47;
  int D4 = -40;
  int D5 = 390;
  int D6 =  47;

  TUNE(SetRange(   0, 600), A1, B5, C1, C4, D2, D5);
  TUNE(SetRange(-500,   0), A2, A4, B2, B3);
  TUNE(SetRange(-300, 300), A3, A5, A6, B1, B4, B6, C2, C3, C5, C6, D1, D3, D4, D6);

  // Endgame evaluation and scaling functions are accessed directly and not through
  // the function maps because they correspond to more than one material hash key.
  Endgame<KXK>    EvaluateKXK[] = { Endgame<KXK>(WHITE),    Endgame<KXK>(BLACK) };

  Endgame<KBPsK>  ScaleKBPsK[]  = { Endgame<KBPsK>(WHITE),  Endgame<KBPsK>(BLACK) };
  Endgame<KQKRPs> ScaleKQKRPs[] = { Endgame<KQKRPs>(WHITE), Endgame<KQKRPs>(BLACK) };
  Endgame<KPsK>   ScaleKPsK[]   = { Endgame<KPsK>(WHITE),   Endgame<KPsK>(BLACK) };
  Endgame<KPKP>   ScaleKPKP[]   = { Endgame<KPKP>(WHITE),   Endgame<KPKP>(BLACK) };

  // Helper used to detect a given material distribution
  bool is_KXK(const Position& pos, Color us) {
    return  !more_than_one(pos.pieces(~us))
          && pos.non_pawn_material(us) >= RookValueMg;
  }

  bool is_KBPsK(const Position& pos, Color us) {
    return   pos.non_pawn_material(us) == BishopValueMg
          && pos.count<BISHOP>(us) == 1
          && pos.count<PAWN  >(us) >= 1;
  }

  bool is_KQKRPs(const Position& pos, Color us) {
    return  !pos.count<PAWN>(us)
          && pos.non_pawn_material(us) == QueenValueMg
          && pos.count<QUEEN>(us) == 1
          && pos.count<ROOK>(~us) == 1
          && pos.count<PAWN>(~us) >= 1;
  }

  /// imbalance() calculates the imbalance by comparing the piece count of each
  /// piece type for both colors.
  template<Color Us>
  int imbalance(const int pieceCount[][PIECE_TYPE_NB]) {

    constexpr Color Them = (Us == WHITE ? BLACK : WHITE);

    int bonus = 0;

    // Second-degree polynomial material imbalance, by Tord Romstad
    for (int pt1 = NO_PIECE_TYPE; pt1 <= QUEEN; ++pt1)
    {
        if (!pieceCount[Us][pt1])
            continue;

        int v = 0;

        for (int pt2 = NO_PIECE_TYPE; pt2 <= pt1; ++pt2)
            v +=  QuadraticOurs[pt1][pt2] * pieceCount[Us][pt2]
                + QuadraticTheirs[pt1][pt2] * pieceCount[Them][pt2];

        bonus += pieceCount[Us][pt1] * v;
    }

    int minor_diff  = pieceCount[Us][KNIGHT] + pieceCount[Us][BISHOP] - pieceCount[Them][KNIGHT] - pieceCount[Them][BISHOP];
    int rook_diff   = pieceCount[Us][ROOK]  - pieceCount[Them][ROOK];
    int queen_diff  = pieceCount[Us][QUEEN] - pieceCount[Them][QUEEN];
    int pawn_diff   = pieceCount[Us][PAWN]  - pieceCount[Them][PAWN];
    int total_pawns = pieceCount[Us][PAWN]  + pieceCount[Them][PAWN];

    // We only need to score these imbalances from one side.
    // The position evaluation will evaluate both colors,
    // so one of them will always count it in the score.

    // 3 minors vs 2 rooks
    if(minor_diff == 3 && rook_diff == -2)
    {
        // Separate bonus for queenless case
        if (pieceCount[Us][QUEEN] + pieceCount[Them][QUEEN] == 0)
            bonus += A1 + A2*pawn_diff + A3*total_pawns;
        else
            bonus += A4 + A5*pawn_diff + A6*total_pawns;
    }

    // 3 minors vs queen
    if(minor_diff == 3 && queen_diff == -1)
    {
        // Separate bonus for rookless case
        if (pieceCount[Us][ROOK] + pieceCount[Them][ROOK] == 0)
            bonus += B1 + B2*pawn_diff + B3*total_pawns;
        else
            bonus += B4 + B5*pawn_diff + B6*total_pawns;
    }

    // 2 rooks vs queen
    if(rook_diff == 2 && queen_diff == -1)
    {
        // Separate bonus when there is no minor on board
        if (minor_diff == 0 && pieceCount[Us][BISHOP] + pieceCount[Us][KNIGHT] == 0)
            bonus += C1 + C2*pawn_diff + C3*total_pawns;
        else
            bonus += C4 + C5*pawn_diff + C6*total_pawns;
    }

    // minor+rook vs queen
    if(minor_diff == 1 && rook_diff == 1 && queen_diff == -1)
    {
        // Separate bonus depending on if the enemy queen is assisted by a rook or not
        if (pieceCount[Them][ROOK] == 0)
            bonus += D1 + D2*pawn_diff + D3*total_pawns;
        else
            bonus += D4 + D5*pawn_diff + D6*total_pawns;
    }

    return bonus;
  }

} // namespace

namespace Material {

/// Material::probe() looks up the current position's material configuration in
/// the material hash table. It returns a pointer to the Entry if the position
/// is found. Otherwise a new Entry is computed and stored there, so we don't
/// have to recompute all when the same material configuration occurs again.

Entry* probe(const Position& pos) {

  Key key = pos.material_key();
  Entry* e = pos.this_thread()->materialTable[key];

  if (e->key == key)
      return e;

  std::memset(e, 0, sizeof(Entry));
  e->key = key;
  e->factor[WHITE] = e->factor[BLACK] = (uint8_t)SCALE_FACTOR_NORMAL;

  Value npm_w = pos.non_pawn_material(WHITE);
  Value npm_b = pos.non_pawn_material(BLACK);
  Value npm = std::max(EndgameLimit, std::min(npm_w + npm_b, MidgameLimit));

  // Map total non-pawn material into [PHASE_ENDGAME, PHASE_MIDGAME]
  e->gamePhase = Phase(((npm - EndgameLimit) * PHASE_MIDGAME) / (MidgameLimit - EndgameLimit));

  // Let's look if we have a specialized evaluation function for this particular
  // material configuration. Firstly we look for a fixed configuration one, then
  // for a generic one if the previous search failed.
  if ((e->evaluationFunction = pos.this_thread()->endgames.probe<Value>(key)) != nullptr)
      return e;

  for (Color c = WHITE; c <= BLACK; ++c)
      if (is_KXK(pos, c))
      {
          e->evaluationFunction = &EvaluateKXK[c];
          return e;
      }

  // OK, we didn't find any special evaluation function for the current material
  // configuration. Is there a suitable specialized scaling function?
  const EndgameBase<ScaleFactor>* sf;

  if ((sf = pos.this_thread()->endgames.probe<ScaleFactor>(key)) != nullptr)
  {
      e->scalingFunction[sf->strongSide] = sf; // Only strong color assigned
      return e;
  }

  // We didn't find any specialized scaling function, so fall back on generic
  // ones that refer to more than one material distribution. Note that in this
  // case we don't return after setting the function.
  for (Color c = WHITE; c <= BLACK; ++c)
  {
    if (is_KBPsK(pos, c))
        e->scalingFunction[c] = &ScaleKBPsK[c];

    else if (is_KQKRPs(pos, c))
        e->scalingFunction[c] = &ScaleKQKRPs[c];
  }

  if (npm_w + npm_b == VALUE_ZERO && pos.pieces(PAWN)) // Only pawns on the board
  {
      if (!pos.count<PAWN>(BLACK))
      {
          assert(pos.count<PAWN>(WHITE) >= 2);

          e->scalingFunction[WHITE] = &ScaleKPsK[WHITE];
      }
      else if (!pos.count<PAWN>(WHITE))
      {
          assert(pos.count<PAWN>(BLACK) >= 2);

          e->scalingFunction[BLACK] = &ScaleKPsK[BLACK];
      }
      else if (pos.count<PAWN>(WHITE) == 1 && pos.count<PAWN>(BLACK) == 1)
      {
          // This is a special case because we set scaling functions
          // for both colors instead of only one.
          e->scalingFunction[WHITE] = &ScaleKPKP[WHITE];
          e->scalingFunction[BLACK] = &ScaleKPKP[BLACK];
      }
  }

  // Zero or just one pawn makes it difficult to win, even with a small material
  // advantage. This catches some trivial draws like KK, KBK and KNK and gives a
  // drawish scale factor for cases such as KRKBP and KmmKm (except for KBBKN).
  if (!pos.count<PAWN>(WHITE) && npm_w - npm_b <= BishopValueMg)
      e->factor[WHITE] = uint8_t(npm_w <  RookValueMg   ? SCALE_FACTOR_DRAW :
                                 npm_b <= BishopValueMg ? 4 : 14);

  if (!pos.count<PAWN>(BLACK) && npm_b - npm_w <= BishopValueMg)
      e->factor[BLACK] = uint8_t(npm_b <  RookValueMg   ? SCALE_FACTOR_DRAW :
                                 npm_w <= BishopValueMg ? 4 : 14);

  // Evaluate the material imbalance. We use PIECE_TYPE_NONE as a place holder
  // for the bishop pair "extended piece", which allows us to be more flexible
  // in defining bishop pair bonuses.
  const int pieceCount[COLOR_NB][PIECE_TYPE_NB] = {
  { pos.count<BISHOP>(WHITE) > 1, pos.count<PAWN>(WHITE), pos.count<KNIGHT>(WHITE),
    pos.count<BISHOP>(WHITE)    , pos.count<ROOK>(WHITE), pos.count<QUEEN >(WHITE) },
  { pos.count<BISHOP>(BLACK) > 1, pos.count<PAWN>(BLACK), pos.count<KNIGHT>(BLACK),
    pos.count<BISHOP>(BLACK)    , pos.count<ROOK>(BLACK), pos.count<QUEEN >(BLACK) } };

  e->value = int16_t((imbalance<WHITE>(pieceCount) - imbalance<BLACK>(pieceCount)) / 16);
  return e;
}

} // namespace Material
