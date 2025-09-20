-- define nats as a list of natural numbers
nats = 0 : [x + 1 | x <- nats]

-- list of nats is 0 appended to the list of all nats plus 1
