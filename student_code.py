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

        # for f in self.facts:
        #     if f.statement == fact_or_rule
        if factq(fact_or_rule):
            if fact_or_rule in self.facts:
                new_fact_or_rule = self.facts[self.facts.index(fact_or_rule)]
            else:
                return
        elif isinstance(fact_or_rule, Rule):
            if fact_or_rule in self.rules:
                new_fact_or_rule = self.rules[self.rules.index(fact_or_rule)]
            else:
                return

        if factq(new_fact_or_rule):
            if new_fact_or_rule.asserted == True:
                # print("this fact was asserted")
                # print(len(fact_or_rule.supported_by))
                # print(len(fact_or_rule.supports_facts))
                # print(len(fact_or_rule.supports_rules))

                if len(new_fact_or_rule.supported_by) == 0:
                    for supportedFact in new_fact_or_rule.supports_facts:
                        # print(supportedFact)
                        for pair in supportedFact.supported_by:
                            if pair[0] == new_fact_or_rule:
                                supportedFact.supported_by.remove(pair)
                                self.kb_retract(supportedFact)
                    for supportedRule in new_fact_or_rule.supports_rules:
                        for pair in supportedRule.supported_by:
                            if pair[0] == new_fact_or_rule:
                                supportedRule.supported_by.remove(pair)
                                self.kb_retract(supportedRule)
                    self.facts.remove(new_fact_or_rule)
                else:
                    new_fact_or_rule.asserted = False
            else:
                # print("this fact was not asserted")
                if len(new_fact_or_rule.supported_by) == 0:
                    # print("boo suckers")
                    for supportedFact2 in new_fact_or_rule.supports_facts:
                        for pair in supportedFact2.supported_by:
                            if pair[0] == new_fact_or_rule:
                                supportedFact2.supported_by.remove(pair)
                                self.kb_retract(supportedFact2)
                    for supportedRule2 in new_fact_or_rule.supports_rules:
                        for pair in supportedRule2.supported_by:
                            if pair[0] == new_fact_or_rule:
                                supportedRule2.supported_by.remove(pair)
                                self.kb_retract(supportedRule2)
                    self.facts.remove(new_fact_or_rule)
        else:
            if new_fact_or_rule.asserted == True:
                pass
            else:
                # print(new_fact_or_rule)
                if len(new_fact_or_rule.supported_by) == 0:
                    # print("boo suckers")
                    # print(new_fact_or_rule)
                    for supportedFact3 in new_fact_or_rule.supports_facts:
                        # print(supportedFact3)
                        for pair in supportedFact3.supported_by:
                            if pair[1] == new_fact_or_rule:
                                supportedFact3.supported_by.remove(pair)
                                self.kb_retract(supportedFact3)
                    for supportedRule3 in new_fact_or_rule.supports_rules:
                        for pair in supportedRule3.supported_by:
                            if pair[1] == new_fact_or_rule:
                                supportedRule3.supported_by.remove(pair)
                                self.kb_retract(supportedRule3)
                    self.rules.remove(new_fact_or_rule)
                # print("this rule was not asserted")



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
                new_fact = Fact(rule_rhs,[(fact,rule)])
                if new_fact not in kb.facts:
                    fact.supports_facts.append(new_fact)
                    rule.supports_facts.append(new_fact)
                    # print(new_fact.statement)
                    # print("adding fact in []")
                    kb.kb_add(new_fact)
                else:
                    new_fact = kb.facts[kb.facts.index(new_fact)]
                    new_fact.supported_by.append((fact,rule))
                    fact.supports_rules.append(new_fact)
                    rule.supports_rules.append(new_fact)
            else:
                new_rule = Rule([rule.lhs[1:],rule_rhs],[(fact,rule)])
                if new_rule not in kb.rules:
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)
                    # print("adding rule in []")
                    kb.kb_add(new_rule)
                else:
                    new_rule = kb.rules[kb.rules.index(new_rule)]
                    new_rule.supported_by.append((fact,rule))
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)

        # Rule has variables instead
        elif new_bindings !=  False:
            if len(rule.lhs) == 1:
                new_statement = instantiate(rule_rhs,new_bindings)
                new_fact = Fact(new_statement,[(fact,rule)])
                if new_fact not in kb.facts:
                    fact.supports_facts.append(new_fact)
                    rule.supports_facts.append(new_fact)
                    # print(new_fact.statement)
                    # print("adding fact in not false")
                    kb.kb_add(new_fact)
                else:
                    new_fact = kb.facts[kb.facts.index(new_fact)]
                    new_fact.supported_by.append((fact,rule))
                    fact.supports_rules.append(new_fact)
                    rule.supports_rules.append(new_fact)
            else:
                newRulesArray = []
                for oldRule in rule.lhs[1:]:
                    # print(instantiate(oldRule,new_bindings))
                    newRulesArray.append(instantiate(oldRule,new_bindings))
                new_rule = Rule([newRulesArray,instantiate(rule_rhs,new_bindings)],[(fact,rule)])
                if new_rule not in kb.rules:
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)
                    # print("adding rule in not false")
                    kb.kb_add(new_rule)
                else:
                    new_rule = kb.rules[kb.rules.index(new_rule)]
                    new_rule.supported_by.append((fact,rule))
                    fact.supports_rules.append(new_rule)
                    rule.supports_rules.append(new_rule)
        # else:
        #     print("nothing cooking")
