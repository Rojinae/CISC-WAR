from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from nnf import config
import random

# Setting up the SAT solver backend for efficient processing
config.sat_backend = "kissat"
E = Encoding()

# Constants for a standard deck of cards
RANKS = list(range(1, 14))
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
    random.shuffle(shuffled_deck)  # Shuffle the deck once

    midpoint = len(shuffled_deck) // 2
    player_a_cards = shuffled_deck[:midpoint]
    player_b_cards = shuffled_deck[midpoint:]

    # Assign cards to players based on shuffled order
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
    """Enforces core game rules including playing, winning, and tie conditions."""
    for round_number in range(1, 27):  # 26 rounds for each player
        plays_A = [Plays("Player A", card, round_number) for card in deck]
        plays_B = [Plays("Player B", card, round_number) for card in deck]

        # Ensure each player plays exactly one card per round
        E.add_constraint(sum(plays_A) == 1)
        E.add_constraint(sum(plays_B) == 1)

        for card_x in deck:
            for card_y in deck:
                # Players must play cards they own
                E.add_constraint(Plays("Player A", card_x, round_number) >> Owns("Player A", card_x))
                E.add_constraint(Plays("Player B", card_y, round_number) >> Owns("Player B", card_y))

                # Winning and tie conditions
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

        # Enforce mutual exclusivity of outcomes in each round
        E.add_constraint(
            Wins("Player A", round_number) | Wins("Player B", round_number) | Tie(round_number)
        )
        E.add_constraint(
            ~(Wins("Player A", round_number) & Wins("Player B", round_number))
        )

@constraint(E)
def handle_tie_breaking():
    """Implements refined multi-round tie-breaking logic."""
    for round_number in range(1, 27):
        if Tie(round_number):
            tie_resolved = False
            
            for tie_round in range(1, 4):  # Handle up to 3 tie-breaking rounds
                tie_plays_A = [Plays("Player A", card, round_number + tie_round) for card in deck]
                tie_plays_B = [Plays("Player B", card, round_number + tie_round) for card in deck]

                # Ensure each player plays exactly one card per tie-breaker round
                E.add_constraint(sum(tie_plays_A) == 1)
                E.add_constraint(sum(tie_plays_B) == 1)

                for card_x in deck:
                    for card_y in deck:
                        E.add_constraint(
                            (Plays("Player A", card_x, round_number + tie_round) &
                             Plays("Player B", card_y, round_number + tie_round) &
                             HigherRank(card_x, card_y)) >>
                            Wins("Player A", round_number)
                        )
                        E.add_constraint(
                            (Plays("Player B", card_y, round_number + tie_round) &
                             Plays("Player A", card_x, round_number + tie_round) &
                             HigherRank(card_y, card_x)) >>
                            Wins("Player B", round_number)
                        )
                        
                        # Set tie_resolved flag to true if a winner is found
                        tie_resolved = (Wins("Player A", round_number) | Wins("Player B", round_number))

            # If no winner after 3 tie-breaker rounds, mark it as a final tie
            if not tie_resolved:
                E.add_constraint(FinalTie(round_number))
                E.add_constraint(~(Wins("Player A", round_number) | Wins("Player B", round_number)))
                
@constraint(E)
def determine_overall_winner():
    """Determines the overall winner based on total rounds won."""
    total_wins_a = sum([Wins("Player A", r) for r in range(1, 27)])
    total_wins_b = sum([Wins("Player B", r) for r in range(1, 27)])

    # If Player A wins more rounds, they are the overall winner
    E.add_constraint((total_wins_a > total_wins_b) >> OverallWinner("Player A"))
    # If Player B wins more rounds, they are the overall winner
    E.add_constraint((total_wins_b > total_wins_a) >> OverallWinner("Player B"))

@constraint(E)
def setup_stacked_deck_for_player(player):
    """Sets up a stacked deck to maximize wins for the specified player."""
    stacked_cards = sorted(deck, key=lambda c: c.rank, reverse=True)[:26]
    other_cards = sorted(deck, key=lambda c: c.rank)[26:]

    for round_number in range(1, 27):
        if player == "Player A":
            card_a, card_b = stacked_cards[round_number - 1], other_cards[round_number - 1]
        else:
            card_b, card_a = stacked_cards[round_number - 1], other_cards[round_number - 1]

        E.add_constraint(Plays("Player A", card_a, round_number) & Owns("Player A", card_a))
        E.add_constraint(Plays("Player B", card_b, round_number) & Owns("Player B", card_b))
        E.add_constraint(Wins(player, round_number))

def analyze_stacked_deck_outcomes(player):
    """Analyzes outcomes with a stacked deck ensuring wins for the specified player."""
    setup_stacked_deck_for_player(player)
    total_wins = sum([count_solutions(E, Wins(player, r)) for r in range(1, 27)])
    overall_winner = count_solutions(E, OverallWinner(player))

    print(f"Total guaranteed wins for {player} with a stacked deck: {total_wins}")
    print(f"Is {player} the overall winner with a stacked deck? {'Yes' if overall_winner > 0 else 'No'}")
    
if __name__ == "__main__":
    # Run the game setup and analysis
    shuffle_and_setup_deck()  # Setup with a shuffled deck
    enforce_game_rules()
    handle_tie_breaking()
    determine_overall_winner()
    analyze_stacked_deck_outcomes("Player A")
