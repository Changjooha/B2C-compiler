auto main()
{
    auto x = 1;

    {
        auto x = 2.0;
        auto y;

        y = x + 1.0;
    }

    return x;
}
