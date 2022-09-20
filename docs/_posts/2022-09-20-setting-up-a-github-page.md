---
layout: post
title:  "Setting up a Github Page"
date:   2022-09-20 
categories: technical 
---

For running a GitHub pages blog, you need mainly these:

- setting A, AAAA and TXT records for your domain name
- creating a GitHub repository with your username as a name
- set it up for GitHub Pages
- install Ruby and Jekyll on your machine
- create the file structure in your repository's docs directory with Jekyll
- configure basic texts about your blog and the About page
- create your first post 

# Setting DNS records for your domain name

I suggest you to do this first, as these take time to go through DNS servers.
For using your domain name for your blog, you need to set its A records to point to Github's IPv4 addresses
and AAAA records to its IPv6 addresses. The result should be this, using the dig command:

```
$ dig formalisation.org
...
;; ANSWER SECTION:
formalisation.org.      3600    IN      A       185.199.109.153
formalisation.org.      3600    IN      A       185.199.110.153
formalisation.org.      3600    IN      A       185.199.111.153
formalisation.org.      3600    IN      A       185.199.108.153
```
and
```
$ dig formalisation.org -t AAAA
...
;; ANSWER SECTION:
formalisation.org.      3600    IN      AAAA    2606:50c0:8000::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8001::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8002::153
formalisation.org.      3600    IN      AAAA    2606:50c0:8003::153
```



[jekyll-docs]: https://jekyllrb.com/docs/home
[jekyll-gh]:   https://github.com/jekyll/jekyll
[jekyll-talk]: https://talk.jekyllrb.com/
