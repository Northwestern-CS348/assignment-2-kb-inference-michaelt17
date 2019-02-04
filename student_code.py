import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        # print("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        # print("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        # print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        if rule.lhs != []:
            leftHandSide = rule.lhs[0]

        new_bindings = match(fact.statement,leftHandSide)
        rule_rhs = rule.rhs

        # print("lhs0: " + str(leftHandSide))
        # print("rhs: " + str(rule_rhs))
        # print("bindings: " + str(new_bindings))

        # If a rule has already been created with the constants
        if new_bindings == []:
            if len(rule.lhs) == 1:
                new_fact = Fact(rule_rhs,[fact,rule])
                if new_fact not in kb.facts:
                    fact.supports_facts.append(new_fact)
                    rule.supports_facts.append(new_fact)
                    # print("adding fact in []")
                    kb.kb_add(new_fact)
            else:
                new_rule = Rule([rule.lhs[1:],rule_rhs],[fact,rule])
                if new_rule not in kb.rules:
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)
                    # print("adding rule in []")
                    kb.kb_add(new_rule)

        # Rule has bindings instead
        elif new_bindings !=  False:
            if len(rule.lhs) == 1:
                new_statement = instantiate(rule_rhs,new_bindings)
                new_fact = Fact(new_statement,[fact,rule])
                if new_fact not in kb.facts:
                    fact.supports_facts.append(new_fact)
                    rule.supports_facts.append(new_fact)
                    # print("adding fact in false")
                    kb.kb_add(new_fact)
            else:
                newRulesArray = []
                for oldRule in rule.lhs[1:]:
                    # print(instantiate(oldRule,new_bindings))
                    newRulesArray.append(instantiate(oldRule,new_bindings))
                new_rule = Rule([newRulesArray,instantiate(rule_rhs,new_bindings)],[fact,rule])
                if new_rule not in kb.rules:
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)
                    # print("adding rule in false")
                    kb.kb_add(new_rule)

        # if new_bindings != False:
        #     if len(rule.lhs) == 1:
        #         new_statement = instantiate(rule_rhs,new_bindings)
        #         new_fact = Fact(new_statement,[fact,rule])
        #         if new_fact not in kb.facts:
        #             # fact.supports_facts.append(new_fact)
        #             # rule.supports_facts.append(new_fact)
        #             # new_fact.supported_by.append(rule)
        #             # new_fact.supported_by.append(fact)
        #             kb.kb_add(new_fact)
        #     else:
        #         # print("booo")
        #         new_statement = instantiate(leftHandSide,new_bindings)
        #         print("looking at statements and bindings")
        #         print(new_statement)
        #         for factInKB in kb.facts:
        #             print("kb statement: " + str(factInKB.statement))
        #             if new_statement == factInKB.statement:
        #                 print("Statements are the same")
        #                 new_rules_array = []
        #                 for oldRule in rule.lhs[1:]:
        #                     new_rules_array.append(instantiate(oldRule,new_bindings))
        #                 new_rule = Rule([new_rules_array,[instantiate(rule_rhs,new_bindings)]],[fact,rule])
        #                 if new_rule not in kb.rules:
        #                     # fact.supports_rules.append(new_rule)
        #                     # rule.supports_rules.append(new_rule)
        #                     # new_rule.supported_by.append(rule)
        #                     # new_rule.supported_by.append(fact)
        #                     kb.kb_add(new_rule)
