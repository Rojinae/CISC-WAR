from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from nnf import config
import random

# Setting up the SAT solver backend for efficient processing
config.sat_backend = "kissat"
E = Encoding()

# Constants for the deck
RANKS = list(range(1, 14))  # 1 for Ace, 11 for Jack, 12 for Queen, 13 for King
SUITS = ["hearts", "diamonds", "clubs", "spades"]

@proposition(E)
class Card:
    def __init__(self, rank, suit):
        self.rank = rank
        self.suit = suit
    def __repr__(self):
        return f"{self.rank} of {self.suit}"

@proposition(E)
class Owns:
    def __init__(self, player, card):
        self.player = player
        self.card = card
    def __repr__(self):
        return f"{self.player} owns {self.card}"

@proposition(E)
class Plays:
    def __init__(self, player, card, round_number):
        self.player = player
        self.card = card
        self.round_number = round_number
    def __repr__(self):
        return f"{self.player} plays {self.card} in round {self.round_number}"

@proposition(E)
class Wins:
    def __init__(self, player, round_number):
        self.player = player
        self.round_number = round_number
    def __repr__(self):
        return f"{self.player} wins round {self.round_number}"

@proposition(E)
class Tie:
    def __init__(self, round_number):
        self.round_number = round_number
    def __repr__(self):
        return f"Tie in round {self.round_number}"

@proposition(E)
class FinalTie:
    def __init__(self, round_number):
        self.round_number = round_number
    def __repr__(self):
        return f"Final unresolved tie in round {self.round_number}"

@proposition(E)
class HigherRank:
    def __init__(self, card1, card2):
        self.card1 = card1
        self.card2 = card2
    def __repr__(self):
        return f"{self.card1} > {self.card2}"

@proposition(E)
class SameRank:
    def __init__(self, card1, card2):
        self.card1 = card1
        self.card2 = card2
    def __repr__(self):
        return f"{self.card1} == {self.card2}"

@proposition(E)
class OverallWinner:
    def __init__(self, player):
        self.player = player
    def __repr__(self):
        return f"Overall winner is {self.player}"

# Global deck of cards
deck = [Card(rank, suit) for rank in RANKS for suit in SUITS]

def shuffle_and_setup_deck():
    """Shuffles the deck once and sets up initial ownership."""
    shuffled_deck = deck.copy()
    random.shuffle(shuffled_deck)

    midpoint = len(shuffled_deck) // 2
    player_a_cards = shuffled_deck[:midpoint]
    player_b_cards = shuffled_deck[midpoint:]

    for card in player_a_cards:
        E.add_constraint(Owns("Player A", card))
    for card in player_b_cards:
        E.add_constraint(Owns("Player B", card))

@constraint(E)
def setup_rank_comparisons():
    """Defines higher and same rank constraints for all card pairs."""
    for card_x in deck:
        for card_y in deck:
            if card_x.rank > card_y.rank:
                E.add_constraint(HigherRank(card_x, card_y))
            elif card_x.rank == card_y.rank:
                E.add_constraint(SameRank(card_x, card_y))

@constraint(E)
def enforce_game_rules():
    """Core game rules including playing, winning, and tie conditions."""
    for round_number in range(1, 27):
        plays_A = [Plays("Player A", card, round_number) for card in deck]
        plays_B = [Plays("Player B", card, round_number) for card in deck]

        E.add_constraint(one_of(plays_A))
        E.add_constraint(one_of(plays_B))

        for card_x in deck:
            for card_y in deck:
                E.add_constraint(Plays("Player A", card_x, round_number) >> Owns("Player A", card_x))
                E.add_constraint(Plays("Player B", card_y, round_number) >> Owns("Player B", card_y))

                E.add_constraint(
                    (Plays("Player A", card_x, round_number) & Plays("Player B", card_y, round_number) & HigherRank(card_x, card_y)) >>
                    Wins("Player A", round_number)
                )
                E.add_constraint(
                    (Plays("Player B", card_y, round_number) & Plays("Player A", card_x, round_number) & HigherRank(card_y, card_x)) >>
                    Wins("Player B", round_number)
                )
                E.add_constraint(
                    (Plays("Player A", card_x, round_number) & Plays("Player B", card_y, round_number) & SameRank(card_x, card_y)) >>
                    Tie(round_number)
                )

        E.add_constraint(Wins("Player A", round_number) | Wins("Player B", round_number) | Tie(round_number))
        E.add_constraint(~(Wins("Player A", round_number) & Wins("Player B", round_number)))

@constraint(E)
def handle_tie_breaking():
    """Improved tie-breaking logic using quantifiers."""
    for round_number in range(1, 27):
        E.add_constraint(
            Tie(round_number) >>
            resolve_tie_with_quantifiers(round_number)
        )

def resolve_tie_with_quantifiers(initial_round):
    """Recursive resolution of ties using quantifiers."""
    constraints = []
    tie_round = 0

    while True:
        current_round = initial_round + tie_round

        for player in ["Player A", "Player B"]:
            constraints.append(
                all(
                    Plays(player, card, current_round + i)
                    for i, card in enumerate(deck[:3])
                )
            )

        face_up_constraints = []
        for player, opponent in [("Player A", "Player B"), ("Player B", "Player A")]:
            face_up_constraints.append(
                any(
                    Plays(player, card, current_round + 3) &
                    ~Owns(opponent, card)
                    for card in deck
                )
            )
        constraints.append(all(face_up_constraints))

        decisive_constraints = []
        for card_x in deck:
            for card_y in deck:
                decisive_constraints.append(
                    (Plays("Player A", card_x, current_round + 3) &
                     Plays("Player B", card_y, current_round + 3) &
                     HigherRank(card_x, card_y)) >>
                    Wins("Player A", initial_round)
                )
                decisive_constraints.append(
                    (Plays("Player B", card_x, current_round + 3) &
                     Plays("Player A", card_y, current_round + 3) &
                     HigherRank(card_x, card_y)) >>
                    Wins("Player B", initial_round)
                )
        constraints.append(any(decisive_constraints))

        if Wins("Player A", initial_round) or Wins("Player B", initial_round):
            break

        tie_round += 4

    constraints.append(
        ~Wins("Player A", initial_round) & ~Wins("Player B", initial_round) >>
        FinalTie(initial_round)
    )

    return all(constraints)

@constraint(E)
def determine_overall_winner():
    """Determines the overall winner based on total rounds won."""
    total_wins_a = sum([Wins("Player A", r) for r in range(1, 27)])
    total_wins_b = sum([Wins("Player B", r) for r in range(1, 27)])

    E.add_constraint((total_wins_a > total_wins_b) >> OverallWinner("Player A"))
    E.add_constraint((total_wins_b > total_wins_a) >> OverallWinner("Player B"))
    E.add_constraint((total_wins_a == total_wins_b) >> FinalTie("game"))

def one_of(plays):
    """Ensures exactly one of the given plays occurs."""
    return any(plays) & all(~plays[i] | ~plays[j] for i in range(len(plays)) for j in range(len(plays)) if i != j)
    
def biased_shuffle():
    """Biased shuffle to provide strategic advantages."""
     # Separate high cards and others
    high_cards = [card for card in deck if card.rank in [10, 11, 12, 13, 1]]  # High cards: 10, Jack, Queen, King, Ace
    other_cards = [card for card in deck if card.rank not in [10, 11, 12, 13, 1]]
    
    # Shuffle both pools
    random.shuffle(high_cards)
    random.shuffle(other_cards)
    
    # Ensuring that the number of high cards to A does not exceed available high cards
    high_cards_to_a = min(high_cards_to_a, len(high_cards), total_high_cards)
    high_cards_to_b = total_high_cards - high_cards_to_a
    
    # Build a biased deck: a specific number of high cards to Player A, rest to Player B
    biased_deck = high_cards[:high_cards_to_a] + other_cards + high_cards[-high_cards_to_b:]
    random.shuffle(biased_deck)  # Optional: Shuffle the biased deck to mix high cards within each player's portion

    return biased_deck

def setup_strategic_card_distribution():
    """Distribute cards strategically after a biased shuffle."""
    biased_deck = biased_shuffle(high_cards_to_a=15, total_high_cards=20)
    midpoint = len(biased_deck) // 2
    player_a_cards = biased_deck[:midpoint]
    player_b_cards = biased_deck[midpoint:]
    for card in player_a_cards:
        E.add_constraint(Owns("Player A", card))
    for card in player_b_cards:
        E.add_constraint(Owns("Player B", card))
        
def enforce_variable_win_conditions():
    """Add additional win conditions based on sequences or card combinations."""
    for round_number in range(1, 27):
        for i in range(len(deck) - 1):
            card_a1 = deck[i]
            card_a2 = deck[i + 1]
            card_b1 = deck[i]
            card_b2 = deck[i + 1]
            # Example of a sequence win condition: two consecutive high cards
            E.add_constraint(
                (Plays("Player A", card_a1, round_number) & Plays("Player A", card_a2, round_number + 1) &
                 HigherRank(card_a1, card_b1) & HigherRank(card_a2, card_b2)) >>
                Wins("Player A", round_number + 1)
            )
            E.add_constraint(
                (Plays("Player B", card_b1, round_number) & Plays("Player B", card_b2, round_number + 1) &
                 HigherRank(card_b1, card_a1) & HigherRank(card_b2, card_a2)) >>
                Wins("Player B", round_number + 1)
            )
def setup_partial_assignments(win_percentage=70, favored_player="Player A"):
    """Adjust the game to favor a specific player according to the specified win percentage."""
    total_rounds = 26  # Assuming a full game involves 26 rounds
    rounds_to_win = int((win_percentage / 100) * total_rounds)
    favored_rounds = random.sample(range(1, total_rounds + 1), rounds_to_win)

    for round_number in favored_rounds:
        for card in deck:
            if card.rank in [10, 11, 12, 13, 1]:  # High cards: 10, Jack, Queen, King, Ace
                E.add_constraint(Plays(favored_player, card, round_number))
                for opponent_card in deck:
                    if opponent_card.rank < card.rank:
                        E.add_constraint(Plays("Player B" if favored_player == "Player A" else "Player A", opponent_card, round_number))
                        E.add_constraint(HigherRank(card, opponent_card) >> Wins(favored_player, round_number))
            else:
                E.add_constraint(Plays(favored_player, card, round_number))
                E.add_constraint(Plays("Player B" if favored_player == "Player A" else "Player A", card, round_number) >> Tie(round_number))

    # Ensure only one card is played by each player per round
    for round_number in range(1, 27):
        E.add_constraint(one_of([Plays("Player A", card, round_number) for card in deck]))
        E.add_constraint(one_of([Plays("Player B", card, round_number) for card in deck]))

def print_results():
    """Prints the results of the simulation."""
    likelihood_winner_a = likelihood(E, OverallWinner("Player A"))
    likelihood_winner_b = likelihood(E, OverallWinner("Player B"))
    print(f"Likelihood of Player A winning: {likelihood_winner_a}")
    print(f"Likelihood of Player B winning: {likelihood_winner_b}")

def run_simulation(tests=10, win_percentage=75, strategy="normal"):
    for _ in range(tests):
        if strategy == "biased":
            setup_strategic_card_distribution()
        else:
            shuffle_and_setup_deck()
        
        setup_rank_comparisons()
        enforce_game_rules()
        enforce_variable_win_conditions()
        setup_partial_assignments(win_percentage=win_percentage, favored_player="Player A")
        handle_tie_breaking()
        determine_overall_winner()
        print_results()

if __name__ == "__main__":
    run_simulation(tests=10, win_percentage=75, strategy="biased")
