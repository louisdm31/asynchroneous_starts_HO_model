import sys

txt = ''
with open(sys.argv[1], 'r') as f:
	txt = f.read()

insid = False
comment = False
for i in range(len(txt)-1, -1, -1):
	comment = (comment or txt[i-1:i+1] == '*)') and txt[i-1:i+1] != '(*'
	insid = insid ^ (not comment and txt[i] == '"')
	if insid and txt[i] in '|':
		txt = txt[:i] + '\\<or>' + txt[i+1:]
	elif insid and txt[i] in ':' and txt[i-1] != ':' and txt[(i+1)%len(txt)] != ':':
		txt = txt[:i] + '\\<in>' + txt[i+1:]
	elif insid and txt[i] in '~':
		txt = txt[:i] + '\\<not>' + txt[i+1:]

with open(sys.argv[1], 'w') as f:
	txt = f.write(txt)
