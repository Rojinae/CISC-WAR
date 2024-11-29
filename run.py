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
    for round_number in range(1, 27):  # Assuming 26 rounds to match the number of cards
        plays_A = [Plays("Player A", card, round_number) for card in deck]
        plays_B = [Plays("Player B", card, round_number) for card in deck]

        # Ensure each player plays exactly one card per round
        E.add_constraint(one_of(plays_A))
        E.add_constraint(one_of(plays_B))

        for card_x in deck:
            for card_y in deck:
                # Players must play cards they own
                E.add_constraint(Plays("Player A", card_x, round_number) >> Owns("Player A", card_x))
                E.add_constraint(Plays("Player B", card_y, round_number) >> Owns("Player B", card_y))

                # Define win, loss, and tie conditions
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

def one_of(plays):
    """Constructs an 'exactly one' logical constraint for the given plays."""
    return any(plays) & all(~plays[i] | ~plays[j] for i in range(len(plays)) for j in range(len(plays)) if i != j)

@constraint(E)
def handle_tie_breaking():
    """Implements the card-flipping tie-breaking logic where three cards are flipped face down and the fourth face up."""
    for round_number in range(1, 27):
        # Initial tie-check
        if Tie(round_number):
            tie_round = 1
            while True:
                # Flip 3 cards face down (not compared), fourth card is compared
                down_cards_A = [Plays("Player A", card, round_number + tie_round + i) for i, card in enumerate(deck[:3])]
                down_cards_B = [Plays("Player B", card, round_number + tie_round + i) for i, card in enumerate(deck[:3])]
                decisive_card_A = Plays("Player A", deck[3], round_number + tie_round + 3)
                decisive_card_B = Plays("Player B", deck[3], round_number + tie_round + 3)

                # Enforce that each player flips three cards before the decisive comparison
                E.add_constraint(sum(down_cards_A) == 3)
                E.add_constraint(sum(down_cards_B) == 3)
                
                # Ensure each player plays exactly one card for comparison
                E.add_constraint(sum([decisive_card_A]) == 1)
                E.add_constraint(sum([decisive_card_B]) == 1)

                for card_x in deck:
                    for card_y in deck:
                        # Tie-breaking win conditions for the decisive card
                        E.add_constraint(
                            (decisive_card_A & decisive_card_B & HigherRank(card_x, card_y)) >>
                            Wins("Player A", round_number)
                        )
                        E.add_constraint(
                            (decisive_card_B & decisive_card_A & HigherRank(card_y, card_x)) >>
                            Wins("Player B", round_number)
                        )

                # Exit if a winner is found
                if Wins("Player A", round_number) or Wins("Player B", round_number):
                    break

                # Otherwise, repeat the tie-breaking process with new cards
                tie_round += 4

            # If no winner after multiple rounds of tie-breaking, mark it as a final tie
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
    # Handle tie in overall wins (if needed)
    E.add_constraint((total_wins_a == total_wins_b) >> FinalTie("game"))

@constraint(E)
def setup_stacked_deck_for_player(player):
    """Sets up a stacked deck where the specified player wins every round."""
    # Divide the deck into two halves: one for the stacked player, one for the opponent
    stacked_cards = sorted(deck, key=lambda c: c.rank, reverse=True)[:26]
    other_cards = sorted(deck, key=lambda c: c.rank)[26:]

    for round_number in range(1, 27):
        if player == "Player A":
            # Player A gets the higher-ranked card
            card_a = stacked_cards[round_number - 1]
            card_b = other_cards[round_number - 1]
        else:
            # Player B gets the higher-ranked card
            card_b = stacked_cards[round_number - 1]
            card_a = other_cards[round_number - 1]

        # Player plays the card they own
        E.add_constraint(Plays("Player A", card_a, round_number) & Owns("Player A", card_a))
        E.add_constraint(Plays("Player B", card_b, round_number) & Owns("Player B", card_b))

        # Ensure the stacked player wins each round
        if player == "Player A":
            E.add_constraint(HigherRank(card_a, card_b) >> Wins("Player A", round_number))
        else:
            E.add_constraint(HigherRank(card_b, card_a) >> Wins("Player B", round_number))

def analyze_stacked_deck_outcomes(player):
    """Analyzes outcomes with a stacked deck ensuring wins for the specified player."""
    setup_stacked_deck_for_player(player)
    total_wins = sum([likelihood(E, Wins(player, r)) for r in range(1, 27)])
    overall_winner = likelihood(E, OverallWinner(player))

    print(f"Total guaranteed wins for {player} with a stacked deck: {total_wins}")
    print(f"Is {player} the overall winner with a stacked deck? {'Yes' if overall_winner > 0 else 'No'}")
    
if __name__ == "__main__":
    # Run the game setup and analysis
    shuffle_and_setup_deck()  # Setup with a shuffled deck
    enforce_game_rules()
    handle_tie_breaking()
    determine_overall_winner()
    analyze_stacked_deck_outcomes("Player A")
