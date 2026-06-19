% ======== ES1 ========
even --> bs.
even --> bs, [a], bs, [a], even.

bs --> [].
bs --> [b], bs.

% ======== ES2 ========
s --> [].
s --> [a], s, [d].
s --> t.
t --> [].
t --> [b, b], t, [c, c].

% ======== ES3 ========

prop --> [p].
% prop --> [q].
% prop --> [r].
prop --> [not], prop.
prop --> ['('], prop, [and], prop, [')'].
prop --> ['('], prop, [or], prop, [')'].
prop --> ['('], prop, [implies], prop, [')'].