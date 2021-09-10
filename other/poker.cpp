#include <assert.h>
#include <stdio.h>
#include <utility>
#include <vector>

using std::make_pair;
using std::pair;
using std::vector;

int bsr(int a) {
  return 31 - __builtin_clz(a);
}

// Returns the submask containing highest k bits set.
// Returns -1 instead if  popcnt(a) < k.
int highBits(int a, int k) {
  int b = 0;
  for (int i = 0; i < k; ++i) {
    if (!a) return -1;
    b |= 1 << (31 - __builtin_clz(a));
    a &= ~b;
  }
  return b;
}

constexpr char RANKS_STR[16] = "0123456789TJQKA";
constexpr char SUITS_STR[5] = "CDHS";
enum Poker {
  HIGH_CARD,
  ONE_PAIR,
  TWO_PAIRS,
  THREE_OF_A_KIND,
  STRAIGHT,
  FLUSH,
  FULL_HOUSE,
  FOUR_OF_A_KIND,
  STRAIGHT_FLUSH,
};
constexpr char POKER_STR[9][20] = {
  "HIGH_CARD",
  "ONE_PAIR",
  "TWO_PAIRS",
  "THREE_OF_A_KIND",
  "STRAIGHT",
  "FLUSH",
  "FULL_HOUSE",
  "FOUR_OF_A_KIND",
  "STRAIGHT_FLUSH",
};

// Parses a card in a format as "C2".
// Returns  card = 4 (rank - 2) + suit  (2 <= rank <= 14)
int parseCard(const char *str) {
  int r, s;
  for (r = 2; r < 15; ++r) if (RANKS_STR[r] == str[1]) break;
  assert(r < 15);
  for (s = 0; s < 4; ++s) if (SUITS_STR[s] == str[0]) break;
  assert(s < 4);
  return (r - 2) << 2 | s;
}

// Read a card from standard input.
int readCard() {
  static char buf[3];
  scanf("%s", buf);
  return parseCard(buf);
}

// Returns the best poker hand with the tie-breaker in [0, 2^20).
//   cards must be distinct.
pair<Poker, int> poker(const vector<int> &cards) {
  assert(cards.size() >= 5);
  // a: ranks for all, bs[suit]: ranks, cs[rank]: count, ds[count]: ranks
  int a = 0, bs[4] = {}, cs[15] = {}, ds[5] = {};
  for (const int card : cards) { const int r = (card >> 2) + 2, s = card & 3; a |= bs[s] |= 1 << r; ++cs[r]; }
  for (int r = 2; r < 15; ++r) ds[cs[r]] |= 1 << r;
  // 8. STRAIGHT_FLUSH: highest (5 for A2345)
  {
    int straightFlush = 0;
    for (int s = 0; s < 4; ++s) straightFlush |= bs[s] & bs[s] << 1 & bs[s] << 2 & bs[s] << 3 & (bs[s] << 4 | bs[s] >> 14 << 5);
    if (straightFlush) return make_pair(STRAIGHT_FLUSH, bsr(straightFlush));
  }
  // 7. FOUR_OF_A_KIND: quadruple, other card
  if (ds[4]) {
    const int r4 = bsr(ds[4]);
    return make_pair(FOUR_OF_A_KIND, r4 << 4 | bsr(a ^ 1 << r4));
  }
  // 6. FULL_HOUSE: triple, pair
  if (ds[3]) {
    const int r3 = bsr(ds[3]);
    const int d = (ds[3] ^ 1 << r3) | ds[2];
    if (d) {
      const int r2 = bsr(d);
      return make_pair(FULL_HOUSE, r3 << 4 | r2);
    }
  }
  // 5. FLUSH: 5 highest cards
  {
    int flush = -1;
    for (int s = 0; s < 4; ++s) { const int h = highBits(bs[s], 5); if (flush < h) flush = h; }
    if (flush >= 0) return make_pair(FLUSH, flush);
  }
  // 4. STRAIGHT: highest (5 for A2345)
  {
    const int straight = a & a << 1 & a << 2 & a << 3 & (a << 4 | a >> 14 << 5);
    if (straight) return make_pair(STRAIGHT, bsr(straight));
  }
  // 3. THREE_OF_A_KIND: triple, 2 highest other cards
  if (ds[3]) {
    const int r3 = bsr(ds[3]);
    return make_pair(THREE_OF_A_KIND, r3 << 16 | highBits(a ^ 1 << r3, 2));
  }
  // 2. TWO_PAIRS: larger pair, smaller pair, other card
  // 1. ONE_PAIR: pair, 3 highest other cards
  if (ds[2]) {
    const int r2 = bsr(ds[2]);
    const int d = ds[2] ^ 1 << r2;
    if (d) {
      const int r22 = bsr(d);
      return make_pair(TWO_PAIRS, r2 << 8 | r22 << 4 | bsr(a ^ 1 << r2 ^ 1 << r22));
    }
    return make_pair(ONE_PAIR, r2 << 16 | highBits(a ^ 1 << r2, 3));
  }
  // 0. HIGH_CARD: 5 highest cards
  return make_pair(HIGH_CARD, highBits(a, 5));
}

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>

using std::max;

void unittest(bool stress) {
#define test(c0, c1, c2, c3, c4, hand, tiebreaker) assert(poker({parseCard(c0), parseCard(c1), parseCard(c2), parseCard(c3), parseCard(c4)}) == make_pair(hand, tiebreaker))
  test("CA", "CJ", "CK", "CQ", "CT", STRAIGHT_FLUSH, 14);
  test("DT", "D9", "D8", "D7", "D6", STRAIGHT_FLUSH, 10);
  test("H6", "H2", "H3", "H4", "H5", STRAIGHT_FLUSH, 6);
  test("SA", "S2", "S3", "S4", "S5", STRAIGHT_FLUSH, 5);
  test("CA", "DA", "HA", "SA", "CK", FOUR_OF_A_KIND, 14 << 4 | 13);
  test("C5", "D5", "H5", "S5", "D8", FOUR_OF_A_KIND, 5 << 4 | 8);
  test("HA", "SA", "CA", "DQ", "HQ", FULL_HOUSE, 14 << 4 | 12);
  test("SJ", "CJ", "DJ", "HA", "SA", FULL_HOUSE, 11 << 4 | 14);
  test("CA", "CK", "CQ", "CJ", "C9", FLUSH, 1 << 14 | 1 << 13 | 1 << 12 | 1 << 11 | 1 << 9);
  test("DA", "DK", "D4", "D3", "D2", FLUSH, 1 << 14 | 1 << 13 | 1 << 4 | 1 << 3 | 1 << 2);
  test("HA", "SJ", "HK", "SQ", "HT", STRAIGHT, 14);
  test("CT", "D9", "H8", "C7", "D6", STRAIGHT, 10);
  test("H6", "S2", "H3", "C4", "D5", STRAIGHT, 6);
  test("HA", "H2", "S3", "S4", "S5", STRAIGHT, 5);
  test("CA", "DA", "HA", "SK", "CQ", THREE_OF_A_KIND, 14 << 16 | 1 << 13 | 1 << 12);
  test("C5", "D5", "H5", "S4", "D8", THREE_OF_A_KIND, 5 << 16 | 1 << 8 | 1 << 4);
  test("C2", "H2", "S2", "H3", "H4", THREE_OF_A_KIND, 2 << 16 | 1 << 4 | 1 << 3);
  test("CA", "DA", "CK", "DK", "CQ", TWO_PAIRS, 14 << 8 | 13 << 4 | 12);
  test("CT", "HT", "C6", "D6", "H8", TWO_PAIRS, 10 << 8 | 6 << 4 | 8);
  test("C2", "D2", "H3", "S3", "C4", TWO_PAIRS, 3 << 8 | 2 << 4 | 4);
  test("CA", "SA", "CK", "SQ", "CJ", ONE_PAIR, 14 << 16 | 1 << 13 | 1 << 12 | 1 << 11);
  test("CA", "S9", "C9", "S6", "C3", ONE_PAIR, 9 << 16 | 1 << 14 | 1 << 6 | 1 << 3);
  test("D2", "H2", "C8", "S5", "C4", ONE_PAIR, 2 << 16 | 1 << 8 | 1 << 5 | 1 << 4);
  test("CA", "DK", "CQ", "CJ", "C9", HIGH_CARD, 1 << 14 | 1 << 13 | 1 << 12 | 1 << 11 | 1 << 9);
  test("DA", "HK", "S4", "C3", "D2", HIGH_CARD, 1 << 14 | 1 << 13 | 1 << 4 | 1 << 3 | 1 << 2);
#undef test
  {
    vector<int> freq(9, 0);
    for (int c0 = 0; c0 < 52; ++c0)
    for (int c1 = c0 + 1; c1 < 52; ++c1)
    for (int c2 = c1 + 1; c2 < 52; ++c2)
    for (int c3 = c2 + 1; c3 < 52; ++c3)
    for (int c4 = c3 + 1; c4 < 52; ++c4)
    {
      const vector<int> cards{c0, c1, c2, c3, c4};
      const pair<Poker, int> result = poker(cards);
      assert(0 <= result.second);
      assert(result.second < 1 << 20);
      ++freq[result.first];
    }
    // https://ja.wikipedia.org/wiki/%E3%83%9D%E3%83%BC%E3%82%AB%E3%83%BC%E3%83%BB%E3%83%8F%E3%83%B3%E3%83%89%E3%81%AE%E4%B8%80%E8%A6%A7
    assert(freq[STRAIGHT_FLUSH] == 40);
    assert(freq[FOUR_OF_A_KIND] == 624);
    assert(freq[FULL_HOUSE] == 3744);
    assert(freq[FLUSH] == 5108);
    assert(freq[STRAIGHT] == 10200);
    assert(freq[THREE_OF_A_KIND] == 54912);
    assert(freq[TWO_PAIRS] == 123552);
    assert(freq[ONE_PAIR] == 1098240);
    assert(freq[HIGH_CARD] == 1302540);
  }
  {
    vector<int> freq(9, 0);
    for (int c0 = 0; c0 < 52; ++c0)
    for (int c1 = c0 + 1; c1 < 52; ++c1)
    for (int c2 = c1 + 1; c2 < 52; ++c2)
    for (int c3 = c2 + 1; c3 < 52; ++c3)
    for (int c4 = c3 + 1; c4 < 52; ++c4)
    for (int c5 = c4 + 1; c5 < 52; ++c5)
    for (int c6 = c5 + 1; c6 < 52; ++c6)
    {
      const vector<int> cards{c0, c1, c2, c3, c4, c5, c6};
      const pair<Poker, int> result = poker(cards);
      assert(0 <= result.second);
      assert(result.second < 1 << 20);
      ++freq[result.first];
      if (stress) {
        assert(max({
          poker({c0, c1, c2, c3, c4}),
          poker({c0, c1, c2, c3, c5}),
          poker({c0, c1, c2, c3, c6}),
          poker({c0, c1, c2, c4, c5}),
          poker({c0, c1, c2, c4, c6}),
          poker({c0, c1, c2, c5, c6}),
          poker({c0, c1, c3, c4, c5}),
          poker({c0, c1, c3, c4, c6}),
          poker({c0, c1, c3, c5, c6}),
          poker({c0, c1, c4, c5, c6}),
          poker({c0, c2, c3, c4, c5}),
          poker({c0, c2, c3, c4, c6}),
          poker({c0, c2, c3, c5, c6}),
          poker({c0, c2, c4, c5, c6}),
          poker({c0, c3, c4, c5, c6}),
          poker({c1, c2, c3, c4, c5}),
          poker({c1, c2, c3, c4, c6}),
          poker({c1, c2, c3, c5, c6}),
          poker({c1, c2, c4, c5, c6}),
          poker({c1, c3, c4, c5, c6}),
          poker({c2, c3, c4, c5, c6}),
        }) == result);
      }
    }
    // https://ja.wikipedia.org/wiki/%E3%83%9D%E3%83%BC%E3%82%AB%E3%83%BC%E3%83%BB%E3%83%8F%E3%83%B3%E3%83%89%E3%81%AE%E4%B8%80%E8%A6%A7
    assert(freq[STRAIGHT_FLUSH] == 41584);
    assert(freq[FOUR_OF_A_KIND] == 224848);
    assert(freq[FULL_HOUSE] == 3473184);
    assert(freq[FLUSH] == 4047644);
    assert(freq[STRAIGHT] == 6180020);
    assert(freq[THREE_OF_A_KIND] == 6461620);
    assert(freq[TWO_PAIRS] == 31433400);
    assert(freq[ONE_PAIR] == 58627800);
    assert(freq[HIGH_CARD] == 23294460);
  }
}

int main() {
  unittest(true);
  return 0;
}
