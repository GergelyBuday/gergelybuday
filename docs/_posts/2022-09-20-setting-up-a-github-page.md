---
layout: post
title:  "Setting up a Github Page"
date:   2022-09-20 
categories: technical 
---

For running a GitHub pages blog, you need mainly these:

- setting A, AAAA and TXT records for your domain name
- install Ruby, Bundler and Jekyll on your machine
- creating a GitHub repository with your username as a name
- set it up for GitHub Pages
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
The guide for this is at [Configuring an apex domain](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/managing-a-custom-domain-for-your-github-pages-site#configuring-an-apex-domain) on docs.github.com.

You need to verify your domain with Github Pages with a custom TXT record, see [Verifying a domain for your user site](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/verifying-your-custom-domain-for-github-pages#verifying-a-domain-for-your-user-site) on docs.github.com .

You need to set A, AAAA and TXT records through your domain registrar's domain administration page.

For checking your TXT record, modify this accordingly:

```
$ dig _github-pages-challenge-username.domain.name +nostats +nocomments +nocmd TXT
```
with adequate username and domain name.

# Installing Ruby, Bundler and Jekyll

Ruby is a popular programming environment for websites. Its plugins are called gems, and an uncautious installation of these can lead to a Dependency Hell.

# Creating a GitHub Pages site

For this, follow [Creating a GitHub Pages site with Jekyll](https://docs.github.com/en/pages/setting-up-a-github-pages-site-with-jekyll/creating-a-github-pages-site-with-jekyll) on docs.github.com .



[jekyll-docs]: https://jekyllrb.com/docs/home
[jekyll-gh]:   https://github.com/jekyll/jekyll
[jekyll-talk]: https://talk.jekyllrb.com/
